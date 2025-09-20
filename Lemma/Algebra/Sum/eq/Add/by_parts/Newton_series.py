from util import *


@apply
def apply(self, pivot=-1, i=None, d=1):
    args, (k, S[0], n) = self.of(Sum[Mul])
    n -= 1
    assert n >= 0
    fk, gk = std.array_split(args, pivot)
    fk = Mul(*fk)
    gk = Mul(*gk)
    if i is None:
        i = self.generate_var(integer=True, excludes={k, n})
    assert d > 0
    return Equal(
        self,
        Sum[k:d]((-1) ** k * Sum[i:k + 1]((-1) ** i * Binomial(k, i) * fk._subs(k, n - i)) * Sum[i:n - k + 1](Binomial(n - i, k) * gk._subs(k, i))) + (-1) ** d * Sum[k:n - d + 1](Sum[i:d + 1]((-1) ** (d - i) * Binomial(d, i) * fk._subs(k, i + k)) * Sum[i:k + 1](Binomial(k - i + d - 1, d - 1) * gk._subs(k, i))))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Logic

    d = Symbol(integer=True, positive=True, given=False)
    n = Symbol(domain=Range(d, oo))
    i, k = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(Sum[k:n + 1](f(k) * g(k)), i=i, d=d)

    Eq.initial = Eq[0].subs(d, 1)

    Eq << Eq.initial.this.find(Sum[Mul[Binomial]]).apply(Algebra.Sum.eq.Add.doit)

    Eq << Algebra.Sum.eq.Add.by_parts.apply(Eq[0].lhs, i=i)

    Eq.induct = Eq[0].subs(d, d + 1)

    Eq << Eq.induct.this.find(Sum[Pow * Sum * Sum]).apply(Algebra.Sum.eq.Add.pop)

    Eq.abel = Eq[0].find(Mul[~Sum]).this.apply(Algebra.Sum.eq.Add.by_parts, slice(1, None), i)

    Eq << Eq.abel.find(Sum - Sum).this.apply(Algebra.AddSumS.eq.Sum_Add_Sum)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Add.eq.Mul)

    Eq << Eq[-1].this.rhs.apply(Discrete.Sum.Binom.telescope)

    Eq << Eq.abel.find(Sum[Tuple, Tuple]).this.apply(Discrete.Sum.Binom.limits.swap.lower)

    Eq << Eq.abel.find(-Sum).find(Sum[Tuple, Tuple]).this.apply(Discrete.Sum.Binom.limits.swap.lower)

    Eq << Eq.abel.rhs.find((~Sum) * Sum).this.apply(Algebra.Sum.limits.subst.Neg, i, d - i).this.rhs.find(Binomial).apply(Discrete.Binom.SDiff)

    Eq << Eq[0].subs(Eq.abel.subs(*Eq[-4:]))

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(-Pow).args[:2].apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], d, 1)

    # https://en.wikipedia.org/wiki/Summation_by_parts




if __name__ == '__main__':
    run()
# created on 2023-06-02
# updated on 2023-06-03
