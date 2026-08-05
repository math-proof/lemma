from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    b = Max(abs(a), abs(b))
    return abs(x) <= b


@prove
def prove(Eq):
    from Lemma import Set, Nat, Int

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Set.Le.Le.of.In_Icc.apply(Eq[0])

    Eq << Int.LeAbs.given.LeNeg.Le.apply(Eq[1])

    Eq << Int.GeAbs.apply(b)

    Eq << LessEqual(abs(b), Max(abs(a), abs(b)), plausible=True)

    Eq << Nat.Le.of.Le.Le.apply(Eq[-2], Eq[-1])

    Eq << Nat.Le.of.Le.Le.apply(Eq[3], Eq[-1])

    Eq << Int.LeNegAbs.apply(a)

    Eq << GreaterEqual(-abs(a), -Max(abs(a), abs(b)), plausible=True)

    Eq << Nat.Ge.of.Ge.Ge.apply(Eq[-2], Eq[-1])
    Eq << Nat.Ge.of.Ge.Ge.apply(Eq[2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-06-30
