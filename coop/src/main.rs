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
// #[to_vmt(prover = "yardbird", timeout = 60, print_vmt = false)]
#[to_vmt::ensures(|z| (z < j).implies(c[z] >= z))]
pub fn array_partial_init(a: Vec<usize>, b: Vec<usize>, mut c: Vec<usize>, n: usize) {
    let mut j: usize = 0;
    for i in 0..n {
        if a[i] == b[i] {
            c[j] = i;
            j += 1;
        }
    }
}

//     #[allow(clippy::absurd_extreme_comparisons)]
//     #[allow(unused_comparisons)]
//     #[to_vmt(prover = "yardbird", timeout = 60, print_vmt = false)]
//     pub fn array_partial_init(
//         a: Vec<usize>,
//         b: Vec<usize>,
//         mut c: Vec<usize>,
//         mut i: usize,
//         mut j: usize,
//         n: usize,
//         z: usize,
//     ) {
//         assert!(i == 0);
//         assert!(j == 0);
//         loop {
//             if i < n {
//                 if a[i] == b[i] {
//                     c[i] = i;
//                     j += 1;
//                 }
//                 i += 1;
//             } else {
//                 break;
//             }
//         }
//         assert!(z >= 0);
//         assert!(z < j);
//         assert!(i >= n);
//         assert!(c[z] >= z);
//     }

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

// #[cfg(feature = "to_vmt")]
// mod verify {
//     use to_vmt::to_vmt;
//     #[to_vmt(prover = "yardbird", timeout = 60, print_vmt = true)]
//     pub fn array_copy(a: Vec<usize>, mut b: Vec<usize>, mut i: usize, n: usize, z: usize) {
//         assert!(i == 0);
//         loop {
//             if i < n {
//                 b[i] = a[i];
//                 i += 1;
//             } else {
//                 break;
//             }
//         }
//         assert!(z > 0);
//         assert!(z < n);
//         assert!(i >= n);
//         assert!(a[z] == b[z]);
//     }

//     #[allow(clippy::manual_memcpy)]
//     // #[to_vmt(prover = "yardbird", timeout = 60, print_vmt = false)]
//     // #[to_vmt::requires(a.len() > n && b.len() > n)]
//     // #[to_vmt::ensures(|z| a[z] == b[z])]
//     pub fn array_copy_nice(a: Vec<usize>, mut b: Vec<usize>, n: usize) {
//         for i in 0..n {
//             b[i] = a[i];
//         }
//     }

//     #[to_vmt(prover = "yardbird", timeout = 60, print_vmt = false)]
//     pub fn array_copy_buggy(a: Vec<usize>, mut b: Vec<usize>, mut i: usize, n: usize, z: usize) {
//         assert!(i == 0);
//         loop {
//             if i < n {
//                 b[i] = 10000;
//                 i += 1;
//             } else {
//                 break;
//             }
//         }
//         assert!(z > 0);
//         assert!(z < n);
//         assert!(i >= n);
//         assert!(a[z] == b[z]);
//     }

// }

// fn main() {
//     #[cfg(feature = "to_vmt")]
//     {
//         verify::array_copy(vec![0, 0, 0], vec![1, 1, 1], 0, 3, 2);
//         verify::array_copy_buggy(vec![0, 0, 0], vec![1, 1, 1], 0, 3, 2);
//         verify::array_split_12(vec![0, 0, 0], 0, 1000, 600, 550);
//         verify::array_partial_init(vec![0, 0], vec![0, 0], vec![0, 0], 0, 0, 3, 1);
//     }
// }
