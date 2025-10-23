from util import *


@apply
def apply(is_positive, eq):
    if is_positive.is_Equal:
        eq, is_positive = is_positive, eq

    x = is_positive.of(Expr > 0)
    lhs, rhs = eq.of(Equal)

    return Equal(lhs * x, rhs * x)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x = Symbol(real=True, given=True)
    f, g, h = Function(real=True)
    Eq << apply(f(x) > 0, Equal(g(x) * f(x), h(x) * f(x) + x))

    Eq << Nat.Ne.of.Gt.apply(Eq[0])

    Eq << Nat.EqMulS.of.Eq.apply(Eq[-1], Eq[1])

    Eq << Eq[2].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)




if __name__ == '__main__':
    run()
# created on 2019-04-02
# updated on 2025-04-20
