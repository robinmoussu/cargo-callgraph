pub fn foo1<F: Fn()>(fct: F) {
    foo2(fct)
}
fn foo2<F: Fn()>(fct: F) {
    fct()
}
pub fn foo3<F: Fn()>(fct: F) {
    foo2(fct)
}

