#[allow(clippy::manual_memcpy)]
#[allow(clippy::absurd_extreme_comparisons)]
#[allow(clippy::needless_range_loop)]
#[to_vmt::ensures(|z| (z < k && i >= n && z >= 0).implies(b[z] <= 0))]
fn array_standard_partition(a: Vec<usize>, mut b: Vec<usize>, n: usize) {
    let mut k: usize = 0;
    for i in 0..n {
        if a[i] <= 0 {
            b[k] = a[i];
            k += 1;
        }
    }
}

#[cfg(test)]
mod verify {
    use super::*;
    use log::Level;
    to_vmt::generate_test!(array_standard_partition, depth = 20);
}
