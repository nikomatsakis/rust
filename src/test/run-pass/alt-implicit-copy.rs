fn main() {
    let x = @{mut a: @10, b: @20};
    alt x {
      @{a, b} { assert *a == 10; (*x).a = @30; assert *a == 30; }
    }
}
