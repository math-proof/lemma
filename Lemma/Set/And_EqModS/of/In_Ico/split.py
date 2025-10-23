from util import *


@apply
def apply(given, right_open=True):
    x, (a, b, d) = given.of(Element[Range])
    if right_open:
        return x >= a, x < b, Equal(x % d, a % d)
    else:
        return x >= a, x <= b - 1, Equal(x % d, a % d)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool, Nat

    x = Symbol(integer=True, given=True)
    a, b = Symbol(integer=True, given=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Element(x, Range(a, b, d)), False)

    Eq << Set.In_Ico.Is.And_EqModS.apply(Eq[0])

    Eq << Bool.Cond.of.Cond.Iff.apply(Eq[0], Eq[-1])

    Eq << Bool.And_And.of.And.apply(Eq[-1], None)

    Eq << Nat.Le_Sub_1.of.Lt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2022-01-01

