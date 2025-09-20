from util import *


@apply
def apply(self):
    (fx, n), (x, S[n]) = self.of(Difference[Pow])
    assert not (fx - x)._has(x)
    return Equal(self, factorial(n))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Logic, Set

    x = Symbol(real=True)
    k = Symbol(integer=True, nonnegative=True)
    t = x ** k
    assert t.is_complex
    assert t.is_extended_real
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Difference(x ** n, (x, n)))

    Eq.initial = Eq[0].subs(n, 0)

    Eq << Eq.initial.this.lhs.doit()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Discrete.Diff.split, 1)

    Eq << Eq[-1].this.lhs.expr.doit()

    Eq << Discrete.Pow.eq.Sum.Binom.Newton.apply((x + 1) ** (n + 1), swap=True) - x ** (n + 1)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Discrete.Diff.eq.Sum)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.split, cond=n.set)

    Eq << Eq[-1].this.find(Factorial).apply(Discrete.Factorial.eq.Mul)

    _k = Symbol('k', domain=Range(n))
    Eq.hypothesis_k = Eq[0].subs(n, _k)

    Eq << Discrete.EqDiff.of.Eq.apply(Eq.hypothesis_k, (x, n - _k))

    Eq << Eq[-1].this.lhs.apply(Discrete.Diff.merge)

    Eq << Eq[-1] * binomial(n + 1, _k)

    Eq << Eq[-1].apply(Algebra.EqSumS.of.Eq, (_k,))

    Eq << Eq[-1].this.lhs.limits_subs(_k, k)

    Eq << Eq[0] * (n + 1)

    Eq << Eq[-1] + Eq[-2]

    Eq << Imply(Eq[0] & Eq.hypothesis_k, Eq.induct, plausible=True)

    Eq << Eq[-1].this.lhs.args[0].apply(Algebra.Cond.given.All, _k)

    Eq << Eq[-1].this.lhs.apply(Set.AllIn_Ico.Cond.given.AllIn_Icc.Le)

    Eq << Logic.Cond.of.Cond.Imp.induct.second.split.All.apply(Eq.initial, Eq[-1], n=n)

    Eq << Eq[0].subs(n, _k)





if __name__ == '__main__':
    run()

# created on 2020-10-12
# updated on 2021-12-01
