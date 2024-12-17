use to_vmt::to_vmt;

#[to_vmt]
fn array_copy(a: Vec<usize>, mut b: Vec<usize>, mut i: usize, n: usize, z: usize) {
    assert!(i == 0);
    loop {
        if i < n {
            b[i] = a[i];
            i += 1;
        } else {
            break;
        }
    }
    assert!(z > 0);
    assert!(z < n);
    assert!(i >= n);
    assert!(a[z] == b[z]);
}

fn main() {
    array_copy(vec![0, 0, 0], vec![1, 1, 1], 0, 3, 2);
}
