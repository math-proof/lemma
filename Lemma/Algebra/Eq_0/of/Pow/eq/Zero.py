from util import *


@apply
def apply(given):
    x, n = given.of(Equal[Expr ** Expr, 0])
    assert n.is_integer and n > 0
    return Equal(x, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** n, 0))

    Eq.hypothesis = Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.lhs.lhs.apply(Algebra.Pow.eq.Mul.split.exponent)
    Eq << Eq[-1].this.lhs.apply(Algebra.OrEqS_0.of.Mul.eq.Zero)

    Eq << Logic.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)
    Eq << Logic.Cond.of.All_Imp.apply(Eq[-1], n=n, start=1)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq.hypothesis)





if __name__ == '__main__':
    run()
# created on 2018-11-03
# updated on 2023-05-21
