from util import *


@apply
def apply(gt_zero, x=None, b=None):
    a = gt_zero.of(Expr > 0)
    assert x.is_real
    assert a.is_real and b.is_real
    return Any[x](a * x + b > 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a > 0, x=x, b=b)

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[0])

    epsilon = Symbol(negative=True)
    Eq << Algebra.Any.given.Cond.subst.apply(Eq[1], x, Eq[2].lhs * -b - epsilon)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << -Eq[0] * epsilon




if __name__ == '__main__':
    run()
# created on 2022-04-03
del Add
from . import Add
