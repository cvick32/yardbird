#[allow(clippy::manual_memcpy)]
#[to_vmt::ensures(|z| (z < n && z >= 0 && i >= n).implies(c[z] == a[z] + b[z]))]
fn array_copy_sum(a: Vec<usize>, b: Vec<usize>, mut c: Vec<usize>, n: usize) {
    for i in 0..n {
        c[i] = a[i] + b[i];
    }
}

#[cfg(test)]
mod verify {
    use super::*;
    use log::Level;
    to_vmt::generate_test!(array_copy_sum);
}
