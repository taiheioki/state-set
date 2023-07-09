use state_set::States;

#[derive(Debug, PartialEq, Eq, States)]
struct EmptyNamedStruct {}

#[test]
fn empty_named_struct() {
    assert_eq!(EmptyNamedStruct::NUM_STATES, 1);
    assert_eq!(EmptyNamedStruct {}.into_index(), 0);
    assert_eq!(EmptyNamedStruct::from_index(0), Some(EmptyNamedStruct {}));
}

#[derive(Debug, PartialEq, Eq, States)]
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

    assert_eq!(
        NamedStruct::from_index(0),
        Some(NamedStruct::new(false, None))
    );
    assert_eq!(
        NamedStruct::from_index(1),
        Some(NamedStruct::new(false, Some(false)))
    );
    assert_eq!(
        NamedStruct::from_index(2),
        Some(NamedStruct::new(false, Some(true)))
    );
    assert_eq!(
        NamedStruct::from_index(3),
        Some(NamedStruct::new(true, None))
    );
    assert_eq!(
        NamedStruct::from_index(4),
        Some(NamedStruct::new(true, Some(false)))
    );
    assert_eq!(
        NamedStruct::from_index(5),
        Some(NamedStruct::new(true, Some(true)))
    );
}

#[derive(Debug, PartialEq, Eq, States)]
struct EmptyUnnamedStruct();

#[test]
fn empty_unnamed_struct() {
    assert_eq!(EmptyUnnamedStruct::NUM_STATES, 1);
    assert_eq!(EmptyUnnamedStruct().into_index(), 0);
    assert_eq!(
        EmptyUnnamedStruct::from_index(0),
        Some(EmptyUnnamedStruct())
    );
}

#[derive(Debug, PartialEq, Eq, States)]
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

    assert_eq!(
        UnnamedStruct::from_index(0),
        Some(UnnamedStruct(false, (), None))
    );
    assert_eq!(
        UnnamedStruct::from_index(1),
        Some(UnnamedStruct(false, (), Some(false)))
    );
    assert_eq!(
        UnnamedStruct::from_index(2),
        Some(UnnamedStruct(false, (), Some(true)))
    );
    assert_eq!(
        UnnamedStruct::from_index(3),
        Some(UnnamedStruct(true, (), None))
    );
    assert_eq!(
        UnnamedStruct::from_index(4),
        Some(UnnamedStruct(true, (), Some(false)))
    );
    assert_eq!(
        UnnamedStruct::from_index(5),
        Some(UnnamedStruct(true, (), Some(true)))
    );
}

#[derive(Debug, PartialEq, Eq, States)]
enum EmptyEnum {}

#[test]
fn empty_enum() {
    assert_eq!(EmptyEnum::NUM_STATES, 0);
}

#[derive(Debug, PartialEq, Eq, States)]
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

    assert_eq!(Enum::from_index(0), Some(Enum::A));
    assert_eq!(Enum::from_index(1), Some(Enum::B));
    assert_eq!(Enum::from_index(2), Some(Enum::C));
}

#[derive(Debug, PartialEq, Eq, States)]
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

    assert_eq!(EnumWithData::from_index(0), Some(EnumWithData::A));
    assert_eq!(EnumWithData::from_index(1), Some(EnumWithData::B()));
    assert_eq!(EnumWithData::from_index(2), Some(EnumWithData::C(false)));
    assert_eq!(EnumWithData::from_index(3), Some(EnumWithData::C(true)));
    assert_eq!(
        EnumWithData::from_index(4),
        Some(EnumWithData::D((), false))
    );
    assert_eq!(EnumWithData::from_index(5), Some(EnumWithData::D((), true)));
    assert_eq!(EnumWithData::from_index(6), Some(EnumWithData::E {}));
    assert_eq!(
        EnumWithData::from_index(7),
        Some(EnumWithData::F { x: false })
    );
    assert_eq!(
        EnumWithData::from_index(8),
        Some(EnumWithData::F { x: true })
    );
    assert_eq!(
        EnumWithData::from_index(9),
        Some(EnumWithData::G { x: (), y: false })
    );
    assert_eq!(
        EnumWithData::from_index(10),
        Some(EnumWithData::G { x: (), y: true })
    );
}
