from util import *


@apply
def apply(ge, eq):
    from Lemma.Algebra.Lt.of.Lt.Eq import swap
    return GreaterEqual(*swap(GreaterEqual, ge, eq))


@prove
def prove(Eq):
    from Lemma import Algebra

    a, x, b = Symbol(real=True)
    # Eq << apply(b >= x, Equal(x, a))
    Eq << apply(b >= x, Equal(a, b))

    Eq << Eq[0] + Eq[1]

    Eq << Eq[-1].this.apply(Algebra.Ge.simp.common_terms)


if __name__ == '__main__':
    run()
# created on 2019-05-15

