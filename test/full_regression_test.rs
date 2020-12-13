#![feature(fn_traits)]

// TODO: add multi-level struct

fn foo() {}
fn get_foo_impl() -> impl Fn() {
    foo
}

fn bar() {}
fn get_bar_ptr() -> fn() {
    bar
}

pub trait WrapperTrait: Fn() {}
pub struct WrapperStruct<Fct>(Fct);
pub trait WrapperTraitWithAssociatedType {
    type Fct: Fn();
    fn get_fct(&self) -> Self::Fct;
}

impl<Fct> WrapperStruct<Fct> {
    pub fn call_1(&self) where Fct:Fn() {
        self.0()
    }
}


impl<Fct> WrapperStruct<Fct> where Fct:Fn() {
    pub fn call_2(&self) {
        self.0()
    }
}

impl<Fct> std::ops::Deref for WrapperStruct<Fct> {
    type Target = Fct;
    fn deref(&self)->&Fct { &self.0 }
}

// ************************************************************ //

pub fn direct_call() {
    foo()
}

pub fn call_from_local() {
    let fct = foo;
    fct()
}

pub fn call_from_local_lambda() {
    let fct = || foo();
    fct()
}

pub fn call_from_local_inline_lambda() {
    (|| {
        foo()
    })()
}

pub fn call_from_argument_generic<Fct: Fn()>(fct: Fct) {
    fct()
}

pub fn call_from_argument_impl(fct: impl Fn()) {
    fct()
}

pub fn call_from_argument_dyn(fct: &dyn Fn()) {
    fct()
}

pub fn call_from_argument_ptr(fct: fn()) {
    fct()
}

pub fn call_from_custom_trait(fct: &dyn WrapperTrait) {
    fct()
}

pub fn call_from_return_of_other_function() {
    let fct = get_foo_impl();
    fct()
}

pub fn call_from_inline_return_of_other_function() {
    get_foo_impl()()
}

pub fn call_from_wrapper_1(fct: WrapperStruct<impl Fn()>) {
    fct.call_1()
}

pub fn call_from_wrapper_2(fct: WrapperStruct<impl Fn()>) {
    fct.call_2()
}

pub fn call_from_wrapper_deref(fct: WrapperStruct<impl Fn()>) {
    fct()
}

pub fn call_fully_qualified_trait_1<Fct: Fn()>(fct: Fct) {
    Fct::call(&fct, ())
}

pub fn call_fully_qualified_trait_2<Fct: Fn()>(fct: Fct) {
    Fn::call(&fct, ())
}

pub fn call_fully_qualified_trait_3<Fct: Fn()>(fct: Fct) {
    fct.call(())
}

pub fn call_trait_with_associated_type(get_fct: impl WrapperTraitWithAssociatedType) {
    let fct = get_fct.get_fct();
    fct()
}

pub fn call_trait_with_associated_type_inline(get_fct: impl WrapperTraitWithAssociatedType) {
    get_fct.get_fct()()
}

pub fn call_from_multiple_local(random: bool) {
    let fct = if random {
        foo
    } else {
        bar
    };
    fct()
}

pub fn call_from_multiple_argument_generic<Fct: Fn()>(f1: Fct, f2: Fct, random: bool) {
    let fct = if random {
        f1
    } else {
        f2
    };
    fct()
}

pub fn call_from_argument_multiple_impl(f1: impl Fn(), f2: impl Fn(), random: bool) {
    let fct: Box<dyn Fn()> = if random {
        Box::new(f1)
    } else {
        Box::new(f2)
    };
    fct()
}

pub fn call_from_argument_multiple_dyn(f1: &dyn Fn(), f2: &dyn Fn(), random: bool) {
    let fct = if random {
        f1
    } else {
        f2
    };
    fct()
}

pub fn call_from_argument_multiple_ptr(f1: fn(), f2: fn(), random: bool) {
    let fct = if random {
        f1
    } else {
        f2
    };
    fct()
}

pub fn call_from_multiple_return_of_other_function(random: bool) {
    let fct: Box<dyn Fn()> = if random {
        Box::new(get_foo_impl())
    } else {
        Box::new(get_bar_ptr())
    };
    fct()
}

pub fn call_mixed_source<
    Fct: Fn(),
    GetFctTrait: Fn() -> Fct,
    // GetFctImpl: Fn() -> impl Fn(), // Not allowed yet
    GetFctDyn: Fn() -> &'static dyn Fn(),
>(
    f1: Fct,
    f2: impl Fn(),
    f3: &dyn Fn(),
    f4: fn(),

    get_trait_trait: GetFctTrait,
    get_impl_trait: impl Fn() -> Fct,
    get_dyn_trait: &dyn Fn() -> Fct,
    get_fn_trait: fn() -> Fct,

    // get_trait_impl: GetFctImpl, // Not allowed yet
    // get_impl_impl: impl Fn() -> impl Fn(), // Not allowed yet
    // get_dyn_impl: &dyn Fn() -> impl Fn(), // Not allowed yet
    // get_fn_impl: fn() -> impl Fn(), // Not allowed yet

    get_trait_dyn: GetFctDyn,
    get_impl_dyn: impl Fn() -> &'static dyn Fn(),
    get_dyn_dyn: &dyn Fn() -> &'static dyn Fn(),
    get_fn_dyn: fn() -> &'static dyn Fn(),

    custom_trait: &dyn WrapperTrait,
    wrapper_1: WrapperStruct<impl Fn()>,
    wrapper_2: WrapperStruct<impl Fn()>,
    wrapper_deref: WrapperStruct<impl Fn()>,
    trait_with_associated_type: impl WrapperTraitWithAssociatedType,

    random: usize)
{
    let fct: Box<dyn Fn()> = match random {
        0 => Box::new(foo),
        1 => Box::new(|| bar()),
        2 => Box::new(get_foo_impl()),
        3 => Box::new(get_bar_ptr()),

        4 => Box::new(f1),
        5 => Box::new(f2),
        6 => Box::new(f3),
        7 => Box::new(f4),

        8 => Box::new(get_trait_trait()),
        9 => Box::new(get_impl_trait()),
        10 => Box::new(get_dyn_trait()),
        11 => Box::new(get_fn_trait()),

        // 12 => Box::new(get_trait_impl()), // Not allowed yet
        // 13 => Box::new(get_impl_impl()), // Not allowed yet
        // 14 => Box::new(get_dyn_impl()), // Not allowed yet
        // 15 => Box::new(get_fn_impl()), // Not allowed yet

        16 => {
            let fct = get_trait_dyn();
            Box::new(fct)
        },
        17 => {
            let fct = get_impl_dyn();
            Box::new(fct)
        },
        18 => {
            let fct = get_dyn_dyn();
            Box::new(fct)
        },
        19 => {
            let fct = get_fn_dyn();
            Box::new(fct)
        },

        20 => Box::new(custom_trait),
        21 => Box::new(|| wrapper_1.call_1()),
        22 => Box::new(|| wrapper_2.call_2()),
        23 => Box::new(&*wrapper_deref),
        24 => Box::new(|| Fct::call(&f1, ())),
        25 => Box::new(|| Fn::call(&f1, ())),
        26 => Box::new(|| f1.call(())),
        27 => Box::new(trait_with_associated_type.get_fct()),

        _ => unimplemented!(),
    };
    fct()
}
