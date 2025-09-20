from util import *


@apply
def apply(self):
    (expr, *limits_s), *limits_i = self.of(Integral[Sum])

    return Equal(self, Sum(Integral(expr, *limits_i), *limits_s), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Logic

    n = Symbol(integer=True, nonnegative=True, given=False)
    k = Symbol(integer=True)
    x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x:a:b](Sum[k:n](f[k](x))))

    Eq << Eq[0].subs(n, 0)

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.eq.Add)

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq << Logic.Eq_Ite.of.All_Imp.apply(Eq[-1], n)


if __name__ == '__main__':
    run()
# created on 2023-04-04
