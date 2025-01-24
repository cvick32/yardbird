/*
TODO: implement expr in index
#[allow(clippy::manual_memcpy)]
#[to_vmt::ensures(|z| (i < n && z >= 0 && z <= n * 2).implies(z[z] >= 0))]
fn array_doub_access_init(mut a: Vec<usize>, n: usize) {
    for i in 0..n {
        a[2 * i] = 0;
        a[(2 * i) + 1] = 0;
    }
}

#[cfg(test)]
mod verify {
    use super::*;
    use log::Level;
    to_vmt::generate_test!(array_doub_access_init);
}
 */
