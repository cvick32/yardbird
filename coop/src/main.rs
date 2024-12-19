use to_vmt::to_vmt;

#[to_vmt(prover = "yardbird", timeout = 60)]
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

#[to_vmt(prover = "yardbird", timeout = 60)]
fn array_copy_buggy(a: Vec<usize>, mut b: Vec<usize>, mut i: usize, n: usize, z: usize) {
    assert!(i == 0);
    loop {
        if i < n {
            b[i] = 10000;
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
    array_copy_buggy(vec![0, 0, 0], vec![1, 1, 1], 0, 3, 2);
}
