from util import *


@apply
def apply(is_nonzero, delta_is_zero, fx):
    from Lemma.Algebra.Le.of.Le.Ge.quadratic import quadratic_coefficient
    a = is_nonzero.of(Unequal[0])
    x, = fx.free_symbols - delta_is_zero.free_symbols
    delta = delta_is_zero.of(Equal[0])

    x, S[a], b, c = quadratic_coefficient(fx, x=x)

    assert (b * b - 4 * a * c).expand() == delta.expand()

    return Equal(fx, (sqrt(a) * x + b / (2 * sqrt(a))) ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, a, b, c = Symbol(complex=True, given=True)
    Eq << apply(Unequal(a, 0), Equal(b ** 2 - 4 * a * c, 0), a * x ** 2 + b * x + c)

    Eq << Eq[-1] / a

    Eq <<= Eq[0] & Eq[-1]

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Eq[1].this.apply(Algebra.EqAdd.Is.Eq_Sub)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])
    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)




if __name__ == '__main__':
    run()
# created on 2018-11-12
# updated on 2023-04-05
