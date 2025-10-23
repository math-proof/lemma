from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    assert interval in Interval(1, oo)
    return log(x) >= 0


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat, Nat

    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Element(f(x), Interval(1, oo)))

    Eq << Set.Eq.of.In.definition.apply(Eq[0])

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Set.Ge.of.In_Icc.apply(Eq[0])

    Eq << Nat.Gt_Sub_1.of.Ge.apply(Eq[-1], 0)

    Eq << Nat.Ne.of.Gt.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-17
# updated on 2025-04-20
