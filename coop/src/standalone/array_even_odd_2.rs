#[allow(clippy::manual_memcpy)]
#[to_vmt::ensures(|z| (z < n && z >= 0 && i >= n).implies(a[z] == b[z] || a[z] == c[z]))]
fn array_even_odd_2(a: Vec<usize>, mut b: Vec<usize>, mut c: Vec<usize>, n: usize) {
    for i in 0..n {
        if i % 2 == 0 {
            b[i] = a[i];
            c[i] = 0;
        } else {
            b[i] = 0;
            c[i] = a[i];
        }
    }
}

#[cfg(test)]
mod verify {
    use super::*;
    use log::Level;
    to_vmt::generate_test!(array_even_odd_2, debug_vmt = true);
}
