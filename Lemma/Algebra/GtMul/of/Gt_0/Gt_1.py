from util import *


@apply
def apply(given, t):
    x = given.of(Expr > 0)
    assert t > 1
    return Greater(t * x, x)


@prove
def prove(Eq):
    from Lemma import Algebra, Int, Nat

    a = Symbol(real=True, given=True)
    t = Symbol(integer=True, positive=True, even=True)
    Eq << apply(a > 0, t)

    Eq << Greater(t - 1, 0, plausible=True)

    Eq << Nat.Gt_0.of.Gt_0.Gt_0.apply(Eq[-1], Eq[0])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)
    Eq << Int.Gt.of.Sub.gt.Zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-14
