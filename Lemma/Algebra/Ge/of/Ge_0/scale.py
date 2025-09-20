from util import *


@apply
def apply(given, t):
    x = given.of(Expr >= 0)
    assert t >= 1
    return GreaterEqual(t * x, x)


@prove
def prove(Eq):
    from Lemma import Algebra

    a = Symbol(real=True, given=True)
    t = Symbol(integer=True, positive=True, odd=True)
    Eq << apply(a >= 0, t)

    Eq << GreaterEqual(t - 1, 0, plausible=True)

    Eq << Algebra.Ge_0.of.Ge_0.Ge_0.apply(Eq[-1], Eq[0])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Algebra.Ge.of.Ge_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-06-14
