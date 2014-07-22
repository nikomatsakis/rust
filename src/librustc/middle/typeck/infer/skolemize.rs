/*!
 * Skolemization is the process of replacing unknown variables with
 * fresh types. The idea is that the type, after skolemization,
 * contains no inference variables but instead contains either a value
 * for each variable (if the variable had already fresh "arbitrary"
 * types wherever a variable would have been.
 */

use middle::ty;
use middle::ty_fold;
use middle::ty_fold::TypeFoldable;
use middle::ty_fold::TypeFolder;

use super::InferCtxt;
use super::unify::InferCtxtMethodsForSimplyUnifiableTypes;
use super::unify::SimplyUnifiable;
use super::unify::UnifyKey;

pub struct TypeSkolemizer<'a> {
    infcx: &'a InferCtxt<'a>,
    skolemization_count: uint
}

impl<'a> TypeSkolemizer<'a> {
    pub fn new(infcx: &'a InferCtxt) -> TypeSkolemizer<'a> {
        TypeSkolemizer { infcx: infcx, skolemization_count: 0 }
    }

    fn probe_ty(&mut self, v: ty::TyVid) -> ty::t {
        self.skolemize_if_none(self.infcx.type_variables.borrow().probe(v))
    }

    fn probe_unifiable<V:SimplyUnifiable,K:UnifyKey<Option<V>>>(&mut self, k: K) -> ty::t {
        self.skolemize_if_none(self.infcx.probe_var(k))
    }

    fn skolemize_if_none(&mut self, o: Option<ty::t>) -> ty::t {
        match o {
            Some(t) => t.fold_with(self),
            None => {
                let index = self.skolemization_count;
                self.skolemization_count += 1;
                ty::mk_infer(self.tcx(), ty::SkolemizedTy(index))
            }
        }
    }
}

impl<'a> TypeFolder for TypeSkolemizer<'a> {
    fn tcx<'b>(&'b self) -> &'b ty::ctxt {
        self.infcx.tcx
    }

    fn fold_ty(&mut self, t: ty::t) -> ty::t {
        match ty::get(t).sty {
            ty::ty_infer(ty::TyVar(v)) => {
                self.probe_ty(v)
            }

            ty::ty_infer(ty::IntVar(v)) => {
                self.probe_unifiable(v)
            }

            ty::ty_infer(ty::FloatVar(v)) => {
                self.probe_unifiable(v)
            }

            ty::ty_infer(ty::SkolemizedTy(_)) => {
                self.tcx().sess.bug("Cannot skolemize a skolemized type");
            }

            ty::ty_nil |
            ty::ty_bot |
            ty::ty_bool |
            ty::ty_char |
            ty::ty_int(..) |
            ty::ty_uint(..) |
            ty::ty_float(..) |
            ty::ty_enum(..) |
            ty::ty_box(..) |
            ty::ty_uniq(..) |
            ty::ty_str |
            ty::ty_err |
            ty::ty_vec(..) |
            ty::ty_ptr(..) |
            ty::ty_rptr(..) |
            ty::ty_bare_fn(..) |
            ty::ty_closure(..) |
            ty::ty_trait(..) |
            ty::ty_struct(..) |
            ty::ty_unboxed_closure(..) |
            ty::ty_tup(..) |
            ty::ty_param(..) => {
                ty_fold::super_fold_ty(self, t)
            }
        }
    }
}
