from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    assert x.is_finite
    return Element(log(x), Interval(-oo, oo))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x = Symbol(complex=True)
    f = Function(complex=True)
    Eq << apply(f(x) > 0)

    Eq << Set.IsPositive.of.Gt_0.apply(Eq[0], simplify=None)

    Eq << Set.Eq.of.In.definition.apply(Eq[-1], 'y')

    Eq << Eq[-1].reversed

    Eq << Eq[1].subs(Eq[-1])

    Eq << Algebra.Ne.of.Gt.apply(Eq[0])





if __name__ == '__main__':
    run()
# created on 2023-04-17
# updated on 2025-04-20
