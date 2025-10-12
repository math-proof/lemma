from util import *


@apply
def apply(self, var='k'):
    (xi, (i, S[0], n)), m = self.of(Pow[Sum])
    k = self.generate_var(integer=True, shape=(oo,), var=var)
    return Equal(self, Sum[k[:n]:Equal(ReducedSum(k[:n]), m):CartesianSpace(Range(0, m + 1), n)](
        Factorial(m) / Product[i:n](Factorial(k[i])) * Product[i:n](xi ** k[i])))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Set, Bool, Finset

    n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(complex=True, shape=(oo,))
    i = Symbol(integer=True)
    m = Symbol(integer=True, nonnegative=True)
    Eq << apply(Sum[i:n](x[i]) ** m)

    Eq << Eq[0].subs(n, 1)

    Eq << Eq[1].this.rhs.apply(Algebra.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.find(functions.Bool).apply(Algebra.Bool.eq.Delta)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.base.apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.apply(Discrete.Pow.eq.Sum.Binom.Newton)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Mul.eq.Mul_Sum)

    Eq << Eq[-1].this.find(Product).apply(Algebra.Prod.eq.Mul.pop)

    Eq << Eq[-1].this.find((~Product) ** -1).apply(Algebra.Prod.eq.Mul.pop)

    Eq << Eq[-1].this.rhs.find(Equal[~ReducedSum]).apply(Algebra.ReducedSum.eq.Add.pop)

    Eq << Eq[-1].this.rhs.find(Equal).apply(Algebra.EqAdd.Is.Eq_Sub, lhs=0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.pop.CartesianSpace.Cond)

    k = Eq[-1].lhs.variable
    Eq << Eq[-1].this.rhs.limits_subs(Eq[-1].rhs.variables[1], k)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.Sum_Mul.eq.Mul_Sum)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.rhs().find(And).apply(Set.Eq_Sum.In_CartesianSpace.Is.And)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.limits.absorb)

    Eq << Eq[0].subs(m, m - k)

    Eq << Bool.ImpNot.of.Or.apply(Eq[-1], 1)

    Eq << Eq[-1].this.lhs.apply(Set.In_Ico.given.In.Ico.restrict, upper=m + 1)

    Eq << Eq[-1].this.lhs.apply(Set.In_Icc.Is.InNeg)

    Eq << Eq[-1].this.lhs.apply(Set.In_Icc.Is.InAdd, m)

    Eq << Bool.All.of.Imp.single_variable.apply(Eq[-1])

    Eq << Eq[-1].this.expr * (x[n] ** k / (Factorial(m - k) * Factorial(k)))

    Eq << Eq[-1].this.expr.rhs.find(Sum).apply(Finset.Sum_Mul.eq.Mul_Sum, simplify=1)

    Eq << Algebra.EqSumS.of.All_Eq.apply(Eq[-1])

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Eq.of.Eq.All_Imp.apply(Eq[1], Eq[-1], n, 1)


if __name__ == '__main__':
    run()
# created on 2023-08-20

