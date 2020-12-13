fn main() {
    let fct = get_fct();
    let fct = forward_fct(fct);
    fct();
}

fn foo() {
    bar()
}

fn bar() {
}

fn get_fct() -> impl Fn() {
    foo
}

fn forward_fct<Fct: Fn()>(fct: Fct) -> Fct {
    fct
}
