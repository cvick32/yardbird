#[allow(clippy::absurd_extreme_comparisons)]
#[allow(unused_comparisons)]
#[to_vmt::ensures(|z| (z < j && j <= n).implies(c[z] >= z))]
pub fn array_partial_init(a: Vec<usize>, b: Vec<usize>, mut c: Vec<usize>, n: usize) {
    let mut j: usize = 0;
    for i in 0..n {
        if a[i] == b[i] {
            c[j] = i;
            j += 1;
        }
    }
}

#[cfg(test)]
mod verify {
    use super::*;
    use log::Level;
    to_vmt::generate_test!(array_partial_init);
}
