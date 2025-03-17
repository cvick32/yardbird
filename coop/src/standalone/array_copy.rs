#[allow(clippy::manual_memcpy)]
#[to_vmt::ensures(|z| (z < n).implies(a[z] == b[z]))]
fn array_copy(a: Vec<usize>, mut b: Vec<usize>, n: usize) {
    for i in 0..n {
        b[i] = a[i];
    }
}

#[cfg(test)]
mod verify {
    use super::*;
    use log::Level;
    to_vmt::generate_test!(array_copy, depth = 20);
}
