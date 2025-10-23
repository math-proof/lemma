from util import *


@apply(simplify=None)
def apply(given, *, evaluate=True):
    n, b = given.of(GreaterEqual)
    assert n.is_finite
    assert b > 0
    return Element(1 / n, Interval.Lopen(0, 1 / b), evaluate=evaluate)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat, Nat

    n = Symbol(real=True)
    b = Symbol(real=True, positive=True)
    Eq << apply(n >= b)

    Eq << Set.In_Ico.given.Ge.Lt.apply(Eq[1])

    Eq << Greater(b, 0, plausible=True)

    Eq << Nat.Gt.of.Ge.Gt.apply(Eq[0], Eq[-1])

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[-1])

    Eq << Algebra.GeDiv.of.Gt_0.Ge.apply(Eq[-2], Eq[0])

    Eq << Algebra.GeDiv.of.Gt_0.Ge.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-10-04
