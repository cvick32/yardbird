#[allow(clippy::manual_memcpy)]
#[to_vmt::ensures(|z| (i > cc && z >= 0 && z < 5 * cc).implies(minval <= a[z] || a[z] == 0))]
fn array_tiling_pr5(
    mut a: Vec<usize>,
    mut a1: Vec<usize>,
    mut a2: Vec<usize>,
    mut a3: Vec<usize>,
    mut a4: Vec<usize>,
    cc: usize,
    minval: usize,
) {
    let val1: usize = 1;
    let val2: usize = 3;
    let val3: usize = 7;
    let val4: usize = 5;
    let val5: usize = 2;
    for i in 1..cc {
        if (minval <= val5) {
            a[i] = 1;
        } else {
            a[i] = 0;
        }
        if (minval <= val4) {
            a1[i] = 1;
        } else {
            a1[i] = 0;
        }
        if (minval <= val3) {
            a2[i] = 1;
        } else {
            a2[i] = 0;
        }
        if (minval <= val2) {
            a3[i] = 1;
        } else {
            a3[i] = 0;
        }
        if (minval <= val1) {
            a4[i] = 1;
        } else {
            a4[i] = 0;
        }
    }
}

#[cfg(test)]
mod verify {
    use super::*;
    use log::Level;
    to_vmt::generate_test!(array_tiling_pr5, depth = 20);
}
