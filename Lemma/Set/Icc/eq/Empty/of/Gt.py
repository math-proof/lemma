from util import *


@apply
def apply(given, left_open=False, right_open=False):
    a, b = given.of(Greater)

    return Equal(Interval(a, b, left_open=left_open, right_open=right_open), a.emptySet)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat

    x, y = Symbol(real=True, given=True)
    Eq << apply(x > y)

    Eq << ~Eq[-1]

    Eq << Set.Any_In.of.Ne_Empty.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Set.Le.Le.of.In_Icc)

    Eq << Eq[-1].this.expr.apply(Nat.Le.of.Le.Ge)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-09-10
