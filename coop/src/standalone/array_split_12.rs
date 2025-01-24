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

mod verify {
    use super::*;
    to_vmt::generate_test!(array_split_12, debug_vmt = true);
}
