use to_vmt::to_vmt2;

#[allow(clippy::manual_memcpy)]
// #[to_vmt::ensures(|z| a[z] == b[z])]
#[to_vmt2]
fn array_copy_nice(a: Vec<usize>, mut b: Vec<usize>, n: usize) {
    for i in 0..n {
        b[i] = a[i];
    }
}

// fn __to_vmt_build_model_array_copy_nice() -> VMTModel {
//     VmtilBuilder::default()
//         .var_immut("A")
//         .var_immut("N")
//         .var_mut("b")
//         .for_loop("i", "0", "N", Stmt::store("b", "i", Expr::select("A", "i")))
//         .post_condition(BooleanExpr::forall(
//             "Z",
//             Some("N"),
//             BooleanExpr::binop("=", Expr::select("a", "Z"), Expr::select("b", "Z")),
//         ))
//         .build_model()
// }

fn main() {
    let model = __to_vmt_build_model_array_copy_nice();
    println!("{}", model.as_vmt_string());

    // array_copy_nice(vec![0, 0], vec![1, 1], 2);
}

mod verify {
    use super::*;

    // #[to_vmt::bmc(depth = 10, check = array_copy_nice)]
    fn verify_array_copy_nice() {
        array_copy_nice(vec![0, 0], vec![1, 1], 2);
    }
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

//     // #[to_vmt(prover = "yardbird", timeout = 60, print_vmt = false)]
//     pub fn array_split_12(mut a: Vec<usize>, mut i: usize, mut y: usize, n: usize, z: usize) {
//         assert!(i == 0);
//         assert!(y == 1000);
//         loop {
//             if i < n {
//                 a[i] = i + y;
//                 i += 1;
//                 if i < 500 {
//                     y -= 1;
//                 } else {
//                     y += 1;
//                 }
//             } else {
//                 break;
//             }
//         }
//         assert!(i >= n);
//         assert!(z < n);
//         assert!(z >= 500);
//         assert!((2 * z) == a[z]);
//     }

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
