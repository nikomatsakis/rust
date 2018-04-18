use hir::def_id::DefId;
use ty::error::TypeError;
use ty::relate::{self, Relate, RelateResult, TypeRelation};
use ty::subst::Substs;
use ty::{self, Ty, TyCtxt};

pub type ContextualFoldResult<'tcx, T> = Result<T, TypeError<'tcx>>;

#[derive(Copy, Clone, Debug)]
pub struct TypeContext {
    pub ambient_variance: ty::Variance,

    /// Track the number of binders as descend.
    pub num_binders: usize,
}

impl TypeContext {
    pub fn new() -> TypeContext {
        TypeContext {
            ambient_variance: ty::Variance::Covariant,
            num_binders: 0,
        }
    }
}

pub trait ContextualTypeFolder<'a, 'gcx: 'tcx, 'tcx: 'a>: Sized {
    fn tcx(&self) -> TyCtxt<'a, 'gcx, 'tcx>;

    fn fold<T: Relate<'tcx>>(
        &mut self,
        context: TypeContext,
        a: &T,
    ) -> ContextualFoldResult<'tcx, T> {
        TypeRelation::relate(
            &mut VarianceAdapter {
                folder: self,
                context,
            },
            a,
            a,
        )
    }

    fn fold_ty(
        &mut self,
        context: TypeContext,
        a: Ty<'tcx>,
    ) -> ContextualFoldResult<'tcx, Ty<'tcx>>;

    fn super_fold_ty(
        &mut self,
        context: TypeContext,
        a: Ty<'tcx>,
    ) -> ContextualFoldResult<'tcx, Ty<'tcx>> {
        relate::super_relate_tys(
            &mut VarianceAdapter {
                folder: self,
                context,
            },
            a,
            a,
        )
    }

    fn fold_region(
        &mut self,
        context: TypeContext,
        a: ty::Region<'tcx>,
    ) -> ContextualFoldResult<'tcx, ty::Region<'tcx>>;
}

struct VarianceAdapter<'fold, F: 'fold> {
    folder: &'fold mut F,
    context: TypeContext,
}

impl<'fold, 'a, 'gcx, 'tcx, F> TypeRelation<'a, 'gcx, 'tcx> for VarianceAdapter<'fold, F>
where
    F: ContextualTypeFolder<'a, 'gcx, 'tcx>, 'gcx: 'tcx, 'tcx: 'a,
{
    fn tcx(&self) -> TyCtxt<'a, 'gcx, 'tcx> {
        self.folder.tcx()
    }

    fn tag(&self) -> &'static str {
        "ContextualTypeFolder"
    }

    fn a_is_expected(&self) -> bool {
        true
    }

    fn binders<T>(
        &mut self,
        a: &ty::Binder<T>,
        b: &ty::Binder<T>,
    ) -> RelateResult<'tcx, ty::Binder<T>>
    where
        T: Relate<'tcx>,
    {
        self.context.num_binders += 1;
        let result = ty::Binder(self.relate(a.skip_binder(), b.skip_binder())?);
        self.context.num_binders -= 1;
        Ok(result)
    }

    fn relate_item_substs(
        &mut self,
        item_def_id: DefId,
        a_subst: &'tcx Substs<'tcx>,
        b_subst: &'tcx Substs<'tcx>,
    ) -> RelateResult<'tcx, &'tcx Substs<'tcx>> {
        if self.context.ambient_variance == ty::Variance::Invariant {
            // Avoid fetching the variance if we are in an invariant
            // context; no need, and it can induce dependency cycles
            // (e.g. #41849).
            relate::relate_substs(self, None, a_subst, b_subst)
        } else {
            let opt_variances = self.tcx().variances_of(item_def_id);
            relate::relate_substs(self, Some(&opt_variances), a_subst, b_subst)
        }
    }

    fn relate_with_variance<T: Relate<'tcx>>(
        &mut self,
        variance: ty::Variance,
        a: &T,
        b: &T,
    ) -> RelateResult<'tcx, T> {
        let old_ambient_variance = self.context.ambient_variance;
        self.context.ambient_variance = self.context.ambient_variance.xform(variance);
        let result = self.relate(a, b);
        self.context.ambient_variance = old_ambient_variance;
        result
    }

    fn tys(&mut self, t1: Ty<'tcx>, t2: Ty<'tcx>) -> RelateResult<'tcx, Ty<'tcx>> {
        assert_eq!(t1, t2);
        self.folder.fold_ty(self.context, t1)
    }

    fn regions(
        &mut self,
        r1: ty::Region<'tcx>,
        r2: ty::Region<'tcx>,
    ) -> RelateResult<'tcx, ty::Region<'tcx>> {
        assert_eq!(r1, r2);
        self.folder.fold_region(self.context, r1)
    }
}
