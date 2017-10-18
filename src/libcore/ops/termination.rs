use fmt::Display;

/// Tmp
#[cfg_attr(not(stage0), lang = "termination")]
#[unstable(feature = "termination_trait", issue = "0")]
pub trait Termination {
    /// TMP
    fn report(self) -> i32;
}

const EXIT_FAILURE: i32 = 1;
const EXIT_SUCCESS: i32 = 0;

#[unstable(feature = "termination_trait", issue = "0")]
impl Termination for () {
    fn report(self) -> i32 { EXIT_SUCCESS }
}

#[unstable(feature = "termination_trait", issue = "0")]
impl<T: Termination, E: Display> Termination for Result<T, E> {
    fn report(self) -> i32 {
        match self {
            Ok(val) => val.report(),
            Err(ref _err) => {
                EXIT_FAILURE
            }
        }
    }
}

#[unstable(feature = "termination_trait", issue = "0")]
impl Termination for ! {
    fn report(self) -> i32 { unreachable!(); }
}

#[unstable(feature = "termination_trait", issue = "0")]
impl Termination for bool {
    fn report(self) -> i32 {
        if self { EXIT_SUCCESS } else { EXIT_FAILURE }
    }
}
