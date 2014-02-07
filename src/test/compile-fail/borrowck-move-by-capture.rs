pub fn main() {
    let bar = ~3;
    let _g = || {
        let _h: proc() -> int = proc() *bar; //~ ERROR cannot move out of captured outer variable
    };
}
