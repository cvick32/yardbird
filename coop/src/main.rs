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

#[allow(clippy::absurd_extreme_comparisons)]
#[allow(unused_comparisons)]
#[to_vmt(prover = "yardbird", timeout = 60, print_vmt = false)]
fn array_partial_init(
    a: Vec<usize>,
    b: Vec<usize>,
    mut c: Vec<usize>,
    mut i: usize,
    mut j: usize,
    n: usize,
    z: usize,
) {
    assert!(i == 0);
    assert!(j == 0);
    loop {
        if i < n {
            if a[i] == b[i] {
                c[i] = i;
                j += 1;
            }
            i += 1;
        } else {
            break;
        }
    }
    assert!(z >= 0);
    assert!(z < j);
    assert!(i >= n);
    assert!(c[z] >= z);
}

/// From our investigation, array_min doesn't depend at all on the array
/// theory. No matter the interpretation of Read, the program is correct.
/// For instance, if your Read interpretation was "no matter what I return
/// 2", then m = 2, and your property check m <= a[Z] evaluates to
/// 2 <= 2, which is true.
#[allow(clippy::absurd_extreme_comparisons)]
#[allow(unused_comparisons)]
#[to_vmt(prover = "yardbird", timeout = 60, print_vmt = true)]
fn array_min(a: Vec<usize>, mut i: usize, mut m: usize, n: usize, z: usize) {
    assert!(i == 0);
    assert!(m == 0);
    loop {
        if i < n {
            if a[i] < m {
                m = a[i];
            }
            i += 1;
        } else {
            break;
        }
    }
    assert!(z >= 0);
    assert!(z < n);
    assert!(i >= n);
    assert!(m <= a[z]);
}

fn main() {
    array_copy(vec![0, 0, 0], vec![1, 1, 1], 0, 3, 2);
    array_copy_buggy(vec![0, 0, 0], vec![1, 1, 1], 0, 3, 2);
    array_split_12(vec![0, 0, 0], 0, 1000, 600, 550);
    array_partial_init(vec![0, 0], vec![0, 0], vec![0, 0], 0, 0, 3, 1);
    array_min(vec![12, 14, 2], 0, 0, 3, 2);
}
