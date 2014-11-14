trait Typer<'tcx> {
    fn method(&self, data: &'tcx int) -> &'tcx int { data }
    fn dummy(&self) { }
}

fn g(_: |&Typer|) {
}

fn h() {
    g(|typer| typer.dummy())
}

fn main() { }
