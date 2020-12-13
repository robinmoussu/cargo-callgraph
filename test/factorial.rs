pub fn factorial_iter(target: u64) -> u64 {
    let mut a = 1;

    let mut i = 1;
    while i < target {
        i += 1;
        a *= i;
    }

    a
}

pub fn factorial_recursive(target: u64) -> u64 {
    if target <= 1 {
        return 1;
    }
    target * factorial_recursive(target - 1)
}
