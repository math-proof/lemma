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
        Sum[k:d](Sum[i:k + 1]((-1) ** (k - i) * Binomial(k, i) * fk._subs(k, i)) * Sum[i:k:n + 1](Binomial(i, k) * gk._subs(k, i))) + Sum[k:n - d + 1](Sum[i:d + 1]((-1) ** (d - i) * Binomial(d, i) * fk._subs(k, i + k)) * Sum[i:k + d:n + 1](Binomial(i - k - 1, d - 1) * gk._subs(k, i))))


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

    Eq << Algebra.Sum.eq.Add.Abel.apply(Eq[0].lhs, i=i)

    Eq.induct = Eq[0].subs(d, d + 1)

    Eq << Eq.induct.this.find(Sum[Sum * Sum]).apply(Algebra.Sum.eq.Add.pop)

    Eq.abel = Eq[0].rhs.args[1].this.apply(Algebra.Sum.eq.Add.Abel, slice(1, None), i=i)

    Eq << Eq.abel.find(Sum - Sum).this.apply(Algebra.AddSumS.eq.Sum_Add_Sum)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Add.eq.Mul)

    Eq << Eq[-1].this.rhs.apply(Discrete.Sum.Binom.telescope)

    Eq << Eq.abel.find(Sum[Tuple, Tuple]).this.apply(Algebra.Sum.limits.subst.offset, 1, -d).this.rhs.apply(Discrete.Sum.Binom.limits.swap.upper)

    Eq << Eq.abel.rhs.args[1].find(Sum[Tuple, Tuple]).this.apply(Algebra.Sum.limits.subst.offset, 1, -d).this.rhs.apply(Discrete.Sum.Binom.limits.swap.upper)

    Eq << Eq[0].subs(Eq.abel.subs(*Eq[-3:]))

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], d, 1)

    # https://en.wikipedia.org/wiki/Summation_by_parts



if __name__ == '__main__':
    run()
# created on 2023-06-03
