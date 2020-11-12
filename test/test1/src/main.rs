fn main() {
    let condition = false;
    if condition {
        m1::foo1(m2::bar);
    } else {
        m1::foo3(m2::bar);
    }
}

mod m1 {
    pub fn foo1<F: Fn()>(fct: F) {
        foo2(fct)
    }
    fn foo2<F: Fn()>(fct: F) {
        fct()
    }
    pub fn foo3<F: Fn()>(fct: F) {
        foo2(fct)
    }
}

mod m2 {
    pub fn bar() {
        baz();
    }

    fn baz() {
        println!("hello word");
    }
}

