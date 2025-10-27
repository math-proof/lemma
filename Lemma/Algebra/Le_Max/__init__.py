from util import *


@apply
def apply(x, y, evaluate=False):
    assert x.is_real and y.is_real
    return LessEqual(x, Max(x, y), evaluate=evaluate)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, y = Symbol(real=True)
    Eq << apply(x, y)

    Eq << Eq[0].this.rhs.apply(Nat.Max.eq.IteGe)


if __name__ == '__main__':
    run()
# created on 2023-04-23

del given
from . import given
