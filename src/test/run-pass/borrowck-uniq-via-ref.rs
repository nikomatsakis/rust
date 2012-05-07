fn borrow(_v: &int) {}

fn box_mut(v: &mut ~int) {
    borrow(*v); //! WARNING Illegal borrow: unique value in aliasable, mutable location

}

fn box_rec_mut(v: &{mut f: ~int}) {
    borrow(v.f); //! WARNING Illegal borrow: unique value in aliasable, mutable location
}

fn box_mut_rec(v: &mut {f: ~int}) {
    borrow(v.f); //! WARNING Illegal borrow: unique value in aliasable, mutable location
}

fn box_mut_recs(v: &mut {f: {g: {h: ~int}}}) {
    borrow(v.f.g.h); //! WARNING Illegal borrow: unique value in aliasable, mutable location
}

fn box_imm(v: &~int) {
    borrow(*v); // OK
}

fn box_imm_rec(v: &{f: ~int}) {
    borrow(v.f); // OK
}

fn box_imm_recs(v: &{f: {g: {h: ~int}}}) {
    borrow(v.f.g.h); // OK
}

fn box_const(v: &const ~int) {
    borrow(*v); //! WARNING Illegal borrow: unique value in aliasable, mutable location
}

fn box_rec_const(v: &{const f: ~int}) {
    borrow(v.f); //! WARNING Illegal borrow: unique value in aliasable, mutable location
}

fn box_recs_const(v: &{f: {g: {const h: ~int}}}) {
    borrow(v.f.g.h); //! WARNING Illegal borrow: unique value in aliasable, mutable location
}

fn box_const_rec(v: &const {f: ~int}) {
    borrow(v.f); //! WARNING Illegal borrow: unique value in aliasable, mutable location
}

fn box_const_recs(v: &const {f: {g: {h: ~int}}}) {
    borrow(v.f.g.h); //! WARNING Illegal borrow: unique value in aliasable, mutable location
}

fn main() {
}