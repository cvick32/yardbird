#![allow(unused)]

#[allow(clippy::manual_memcpy)]
#[to_vmt::ensures(|z| (z < n).implies(a[z] == b[z]))]
fn array_copy(a: Vec<usize>, mut b: Vec<usize>, n: usize) {
    for i in 0..n {
        b[i] = a[i];
    }
}

#[allow(clippy::manual_memcpy)]
#[to_vmt::ensures(|z| (z < n).implies(a[z] == b[z]))]
fn array_copy_raw_loop(a: Vec<usize>, mut b: Vec<usize>, n: usize) {
    let mut i: usize = 0;
    loop {
        if i < n {
            b[i] = a[i];
            i += 1;
        } else {
            break;
        }
    }
}

#[allow(clippy::needless_range_loop)]
#[to_vmt::ensures(|z| (z < n).implies(a[z] == b[z]))]
fn array_copy_buggy(a: Vec<usize>, mut b: Vec<usize>, n: usize) {
    for i in 0..n {
        b[i] = 10000;
    }
}

#[allow(clippy::needless_range_loop)]
#[to_vmt::ensures(|z| (500 <= z && z < n).implies(2 * z == a[z]))]
fn array_split_12(mut a: Vec<usize>, n: usize) {
    let mut y: usize = 1000;
    for i in 0..n {
        a[i] = i + y;
        if i < 500 {
            y -= 1;
        } else {
            y += 1;
        }
    }
}

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

fn main() {}

#[cfg(test)]
mod verify {
    use log::Level;

    use super::*;

    to_vmt::generate_test!(array_copy, depth = 20);
    to_vmt::generate_test!(array_copy_buggy, should_fail = true);
    to_vmt::generate_test!(array_copy_raw_loop);
    to_vmt::generate_test!(array_split_12);
    to_vmt::generate_test!(
        array_partial_init,
        logger = Some(Level::Debug),
        debug_vmt = true
    );
}
