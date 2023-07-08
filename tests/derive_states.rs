use state_set::States;

#[derive(States)]
struct EmptyNamedStruct {}

#[test]
fn empty_named_struct() {
    assert_eq!(EmptyNamedStruct::NUM_STATES, 1);
    assert_eq!(EmptyNamedStruct {}.into_index(), 0);
}

#[derive(States)]
struct NamedStruct {
    a: bool,
    b: (),
    c: Option<bool>,
}

impl NamedStruct {
    fn new(a: bool, c: Option<bool>) -> Self {
        Self { a, b: (), c }
    }
}

#[test]
fn named_struct() {
    assert_eq!(NamedStruct::NUM_STATES, 6);

    assert_eq!(NamedStruct::new(false, None).into_index(), 0);
    assert_eq!(NamedStruct::new(false, Some(false)).into_index(), 1);
    assert_eq!(NamedStruct::new(false, Some(true)).into_index(), 2);
    assert_eq!(NamedStruct::new(true, None).into_index(), 3);
    assert_eq!(NamedStruct::new(true, Some(false)).into_index(), 4);
    assert_eq!(NamedStruct::new(true, Some(true)).into_index(), 5);
}

#[derive(States)]
struct EmptyUnnamedStruct();

#[test]
fn empty_unnamed_struct() {
    assert_eq!(EmptyUnnamedStruct::NUM_STATES, 1);
    assert_eq!(EmptyUnnamedStruct().into_index(), 0);
}

#[derive(States)]
struct UnnamedStruct(bool, (), Option<bool>);

#[test]
fn unnamed_struct() {
    assert_eq!(UnnamedStruct::NUM_STATES, 6);

    assert_eq!(UnnamedStruct(false, (), None).into_index(), 0);
    assert_eq!(UnnamedStruct(false, (), Some(false)).into_index(), 1);
    assert_eq!(UnnamedStruct(false, (), Some(true)).into_index(), 2);
    assert_eq!(UnnamedStruct(true, (), None).into_index(), 3);
    assert_eq!(UnnamedStruct(true, (), Some(false)).into_index(), 4);
    assert_eq!(UnnamedStruct(true, (), Some(true)).into_index(), 5);
}

#[derive(States)]
enum EmptyEnum {}

#[test]
fn empty_enum() {
    assert_eq!(EmptyEnum::NUM_STATES, 0);
}

#[derive(States)]
enum Enum {
    A,
    B,
    C,
}

#[test]
fn normal_enum() {
    assert_eq!(Enum::NUM_STATES, 3);

    assert_eq!(Enum::A.into_index(), 0);
    assert_eq!(Enum::B.into_index(), 1);
    assert_eq!(Enum::C.into_index(), 2);
}

#[derive(States)]
enum EnumWithData {
    A,
    B(),
    C(bool),
    D((), bool),
    E {},
    F { x: bool },
    G { x: (), y: bool },
}

#[test]
fn enum_with_data() {
    assert_eq!(EnumWithData::NUM_STATES, 11);

    assert_eq!(EnumWithData::A.into_index(), 0);
    assert_eq!(EnumWithData::B().into_index(), 1);
    assert_eq!(EnumWithData::C(false).into_index(), 2);
    assert_eq!(EnumWithData::C(true).into_index(), 3);
    assert_eq!(EnumWithData::D((), false).into_index(), 4);
    assert_eq!(EnumWithData::D((), true).into_index(), 5);
    assert_eq!(EnumWithData::E {}.into_index(), 6);
    assert_eq!(EnumWithData::F { x: false }.into_index(), 7);
    assert_eq!(EnumWithData::F { x: true }.into_index(), 8);
    assert_eq!(EnumWithData::G { x: (), y: false }.into_index(), 9);
    assert_eq!(EnumWithData::G { x: (), y: true }.into_index(), 10);
}
