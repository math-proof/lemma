from util import *


@apply
def apply(lt, n):
    x, a = lt.of(Greater)
    assert a >= 0
    assert n > 0
    return x ** n > a ** n


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(real=True)
    a = Symbol(real=True, nonnegative=True)
    Eq << apply(x > a, n)

    Eq << Eq[1].subs(n, 1)

    Eq << Eq[1].subs(n, n + 1)

    Eq << Algebra.GtMul.of.Gt.Gt.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Imply(Eq[1], Eq[2], plausible=True)

    Eq << Logic.Cond.of.Cond.All_Imp.apply(Eq[0], Eq[-1], n, 1)




if __name__ == '__main__':
    run()
# created on 2023-04-15
