#[allow(clippy::needless_range_loop)]
#[to_vmt::ensures(|z| (z < n).implies(a[z] == b[z]))]
fn array_copy_buggy(a: Vec<usize>, mut b: Vec<usize>, n: usize) {
    for i in 0..n {
        b[i] = 10000;
    }
}

#[cfg(test)]
mod verify {
    use super::*;
    use log::Level;

    to_vmt::generate_test!(array_copy_buggy, should_fail = true);
}
