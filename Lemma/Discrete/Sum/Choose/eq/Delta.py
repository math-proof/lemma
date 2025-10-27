from util import *


@apply
def apply(self):
    prod, (k, i, n) = self.of(Sum)
    n -= 1
    (S[n], S[i], S[k - i], S[n - k]), exp = prod.of(Multinomial * (-1) ** Expr)

    assert exp == k - i or exp == k + i
    return Equal(self, KroneckerDelta(n, i))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Set, Tensor, Int, Finset

    k = Symbol(integer=True)
    i = Symbol(integer=True, nonnegative=True)
    n = Symbol(domain=Range(i, oo))
    Eq << apply(Sum[k:i:n + 1]((-1) ** (k - i) * Multinomial(n, i, k - i, n - k)))

    x, y, z = Symbol(real=True)
    Eq << Discrete.Pow.eq.Sum.Choose.apply((x + y + z) ** n)

    Eq << Eq[-1].subs(x, -1).subs(y, 1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.pop.CartesianSpace.Cond)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.limits.pop.CartesianSpace.Cond, simplify=None)

    Eq << Eq[-1].this.rhs.find(Equal).apply(Int.EqAdd.Is.Eq_Sub, lhs=slice(1, None))

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Finset.Sum.eq.Sum_MulBool)

    k0, k1, k2 = Eq[-1].rhs.variables
    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Cond.Is.And.subst)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.absorb)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InNeg)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InAdd, n - k2)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.rhs().find(Min).simplify()

    Eq << Eq[-1].this.rhs().find(Max).simplify()

    i_ = Symbol('i', integer=True)
    Eq << Eq[-1].this.rhs.limits_subs(Eq[-1].rhs.variable, i_)

    Eq << Eq[-1].this.rhs.find(Sum).limits_subs(k1, k)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.limits.subst.Neg)

    Eq << Eq[-1].this.rhs.apply(Tensor.Sum.eq.Dot)

    Eq << Eq[-1].this.lhs.apply(Tensor.Pow.eq.Dot.Delta)

    Eq << Tensor.Eq.of.EqDotSStack_Pow.independence.vector.apply(Eq[-1])

    Eq << Algebra.Cond.of.All.subst.apply(Eq[-1], i_, i)

    Eq << Eq[-1].this.find(Multinomial).simplify()

    Eq << Eq[0].this.lhs.apply(Algebra.Sum.limits.subst.offset, i).reversed





if __name__ == '__main__':
    run()
# created on 2023-08-20
# updated on 2023-08-26
