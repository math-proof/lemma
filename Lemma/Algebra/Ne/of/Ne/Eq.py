from util import *


@apply
def apply(ne, eq):
    from Lemma.Algebra.Lt.of.Lt.Eq import swap
    return Unequal(*swap(Unequal, ne, eq))


@prove
def prove(Eq):
    from Lemma import Algebra

    a, x, b = Symbol(real=True)
    # Eq << apply(b > x, Equal(x, a))
    Eq << apply(Unequal(b, x), Equal(a, x))

    Eq << Eq[0] + Eq[1].reversed

    Eq << Eq[-1].this.apply(Algebra.Ne.simp.common_terms)


if __name__ == '__main__':
    run()
# created on 2020-02-04

