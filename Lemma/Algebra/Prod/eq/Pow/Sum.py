from util import *


@apply
def apply(self, simplify=True):
    (b, e), *limits = self.of(Product[Pow])
    assert not b.has(*self.variables)
    return Equal(self, b ** Sum(e, *limits))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f = Function(real=True)
    a = Symbol(real=True)
    Eq << apply(Product[i:n](a ** f(i)))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq[0] * a ** f(n)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Prod.limits.push)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Eq[-1].this.find(Add[Sum]).apply(Algebra.Add.eq.Sum.limits.push)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Eq_Ite.of.All_Imp.apply(Eq[-1], n)




if __name__ == '__main__':
    run()
# created on 2022-01-15
# updated on 2023-03-30
