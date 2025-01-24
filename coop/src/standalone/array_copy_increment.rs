#[allow(clippy::manual_memcpy)]
#[to_vmt::ensures(|z| (z < n && z >= 0 && i >= n).implies(a[z] < b[z]))]
fn array_copy_increment(a: Vec<usize>, mut b: Vec<usize>, n: usize) {
    for i in 0..n {
        b[i] = a[i] + 1;
    }
}

#[cfg(test)]
mod verify {
    use super::*;
    use log::Level;
    to_vmt::generate_test!(array_copy_increment);
}
