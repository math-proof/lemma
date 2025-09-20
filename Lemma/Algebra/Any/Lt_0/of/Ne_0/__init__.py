from util import *


@apply
def apply(ne_zero, x=None, b=None):
    a = ne_zero.of(Unequal[0])
    assert x.is_real
    assert a.is_real and b.is_real
    return Any[x](a * x + b < 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(Unequal(a, 0), x=x, b=b)

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[1], cond=a > 0)

    Eq << Eq[-2].this.lhs.apply(Algebra.Any.Lt_0.of.Gt_0, x=x, b=b)

    Eq << Logic.Imp.And.of.Cond.apply(Eq[0], cond=Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.Lt_0.of.Lt_0.simple, x=x, b=b)




if __name__ == '__main__':
    run()
# created on 2022-04-03
del Add
from . import Add
