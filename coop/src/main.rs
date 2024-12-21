use to_vmt::to_vmt;

#[to_vmt(prover = "yardbird", timeout = 60, print_vmt = false)]
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

#[to_vmt(prover = "yardbird", timeout = 60, print_vmt = false)]
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

//#[to_vmt(prover = "yardbird", timeout = 60, print_vmt = false)]
fn array_split_12(mut a: Vec<usize>, mut i: usize, mut y: usize, n: usize, z: usize) {
    assert!(i == 0);
    assert!(y == 1000);
    loop {
        if i < n {
            a[i] = i + y;
            i += 1;
            if i < 500 {
                y -= 1;
            } else {
                y += 1;
            }
        } else {
            break;
        }
    }
    assert!(i >= n);
    assert!(z < n);
    assert!(z >= 500);
    assert!((2 * z) == a[z]);
}

fn main() {
    array_copy(vec![0, 0, 0], vec![1, 1, 1], 0, 3, 2);
    array_copy_buggy(vec![0, 0, 0], vec![1, 1, 1], 0, 3, 2);
}
