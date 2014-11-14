#![no_std]
#![feature(lang_items)]

#[lang="sized"]
pub trait Sized for Sized? {
    // Empty.
}

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
