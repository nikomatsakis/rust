// check-pass

#![feature(lazy_impl_trait)]

fn main() {}

trait Reader {}

struct Unit<R>(R);
struct ResDwarf<R>(R);

struct Context<R: Reader> {
    dwarf: ResDwarf<R>,
}

struct Range;

struct ResUnit<R>(R);

impl<R: Reader + 'static> Context<R> {
    /// Find the DWARF unit corresponding to the given virtual memory address.
    fn find_dwarf_unit(&self, probe: u64) -> Option<&Unit<R>> {
        for unit in self.find_units(probe) {
            unimplemented!()
        }
        None
    }

    
    fn find_units(&self, probe: u64) -> impl Iterator<Item = &ResUnit<R>> {
        self.find_units_range(probe, probe + 1)
            .map(|(unit, _range)| unit)
    }

    
    fn find_units_range(
        &self,
        probe_low: u64,
        probe_high: u64,
    ) -> impl Iterator<Item = (&ResUnit<R>, &Range)> {
        std::iter::empty()
    }
}