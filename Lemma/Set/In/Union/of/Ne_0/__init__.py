from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    assert x.is_real
    return Element(x, Reals - {0})


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x = Symbol(real=True)
    Eq << apply(Unequal(x, 0))

    Eq << Algebra.Or.of.Ne_0.apply(Eq[0])

    Eq << Eq[-1].this.args[1].apply(Set.IsPositive.of.Gt_0, simplify=None)

    Eq << Eq[-1].this.args[0].apply(Set.IsNegative.of.Lt_0, simplify=None)

    Eq << Set.In.of.Or.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-02

from . import IsReal
