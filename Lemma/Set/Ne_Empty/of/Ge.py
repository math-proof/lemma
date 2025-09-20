from util import *


@apply
def apply(given):
    S_abs, positive = given.of(GreaterEqual)
    assert positive.is_extended_positive
    S = S_abs.of(Card)

    x = S.element_symbol()

    return Unequal(S, S.etype.emptySet)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    S = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Card(S) >= 1)

    Eq << Algebra.Gt.of.Ge.relax.apply(Eq[0], 0)

    Eq << Set.Ne_Empty.of.Gt_0.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-15
