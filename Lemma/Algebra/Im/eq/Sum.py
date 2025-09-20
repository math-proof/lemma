from util import *


@apply
def apply(self):
    expr, *limits = self.of(Im[Sum])
    return Equal(self, Sum(Im(expr), *limits))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True)
    f = Function(complex=True)
    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Im(Sum[k:n](f[k](x))))

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq << Logic.Eq_Ite.of.All_Imp.apply(Eq[-1], n)


if __name__ == '__main__':
    run()
# created on 2023-10-02
