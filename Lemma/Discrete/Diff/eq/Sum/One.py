from util import *


@apply
def apply(self):
    (expr, *limits), (variable, S[1]) = self.of(Difference[Sum])
    rhs = Sum(Difference[variable](expr).simplify(), *limits)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset, Finset, Finset

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    x = Symbol(real=True)
    Eq << apply(Difference[x](Sum[i:n](f[i](x))))

    Eq << Eq[0].this.lhs.doit()

    Eq << Eq[-1].this.rhs.expr.doit()

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Add.eq.AddSumS)


if __name__ == '__main__':
    run()
# created on 2020-10-11
