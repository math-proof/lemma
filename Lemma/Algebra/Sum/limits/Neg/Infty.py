from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Sum)
    return Equal(self, Sum[i](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus

    i = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[i](f(i)))

    n = Symbol(integer=True, nonnegative=True)
    Eq << Algebra.Sum.limits.Neg.apply(Sum[i:-n:n + 1](f(i)))

    Eq << Calculus.EqLimit.of.Eq.apply(Eq[-1], (n, oo))

    Eq << Eq[-1].this.rhs.apply(Calculus.Limit.eq.Sum)

    Eq << Eq[-1].this.lhs.apply(Calculus.Limit.eq.Sum)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()
# created on 2020-03-16
