// Test that we handle binder levels in object types correctly.
// Initially, the reference to `'tcx` in the object type
// `&Typer<'tcx>` was getting an incorrect binder level, yielding
// weird compilation ICEs and so forth.

trait Typer<'tcx> {
    fn method(&self, data: &'tcx int) -> &'tcx int { data }
}

struct Tcx<'tcx> {
    fields: &'tcx int
}

impl<'tcx> Typer<'tcx> for Tcx<'tcx> {
}

fn g<'tcx>(typer: &Typer<'tcx>) {
}

fn check_static_type<'x>(tcx: &Tcx<'x>) {
    g(tcx)
}

fn main() { }
