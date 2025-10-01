from util import *


@apply
def apply(self):
    xi, limit = self.of(Sum ** 2)
    try:
        i, S[0], n = limit.of(Tuple)
    except:
        i, = limit
        domain = xi.domain_defined(i)
        S[0], n = domain.of(Range)

    j = self.generate_var({i}, integer=True, var='j')
    xj = xi._subs(i, j)
    return Equal(self, 2 * Sum[j:i, i:n](xi * xj) + Sum[i:n](xi ** 2))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(Sum[i:n](x[i]) ** 2)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.find(Sum).apply(Algebra.Sum.eq.AddSumS, cond={n})

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.AddSumS, cond={n})

    Eq << Eq[-1].this.rhs.find(Number * ~Sum).apply(Algebra.Sum.eq.AddSumS, cond={n})

    Eq << Eq[-1].this.rhs.find(Number * ~Sum).simplify()

    j = Eq[0].find(Number * ~Sum).variable
    Eq << Eq[-1].this.rhs.find(Indexed * ~Sum).limits_subs(j, i)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.All_Imp.apply(Eq[-1], n=n, start=1)





if __name__ == '__main__':
    run()
# created on 2019-11-03
# updated on 2023-08-26
