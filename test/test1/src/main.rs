pub mod m1;
pub mod m2;

fn main() {
    let condition = false;
    if condition {
        m1::foo1(m2::bar);
    } else {
        m1::foo3(m2::bar);
    }
}
