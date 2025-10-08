from util import *


@apply
def apply(lt, n, evaluate=True):
    x, a = lt.of(Less)
    assert x >= 0
    assert n > 0
    return Less(x ** n, a ** n, evaluate=evaluate)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(real=True, nonnegative=True)
    a = Symbol(real=True)
    Eq << apply(x < a, n)

    Eq << Eq[1].subs(n, 1)

    Eq << Eq[1].subs(n, n + 1)

    Eq << Algebra.LtMul.of.Lt.Lt.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Imply(Eq[1], Eq[2], plausible=True)

    Eq << Bool.Cond.of.Cond.All_Imp.apply(Eq[0], Eq[-1], n, 1)




if __name__ == '__main__':
    run()
# created on 2023-04-15
# updated on 2023-10-04
