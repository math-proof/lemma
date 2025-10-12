from util import *


def rewrite(Sum, self, i=0, j=1):
    assert i < j
    expr, *limits = self.of(Sum)
    i_limit, j_limit = limits[i], limits[j]

    assert not i_limit._has(j_limit[0])
    if j_limit._has(i_limit[0]):
        i = self.expr.generate_var(excludes=self.variables, **i_limit[0].type.dict)
        expr = expr._subs(i_limit[0], i)
        i_limit = (i, *i_limit[1:])

    limits[i], limits[j] = j_limit, i_limit
    return Sum(expr, *limits)

@apply
def apply(self, i=0, j=1):
    return Equal(self, rewrite(Sum, self, i, j))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Finset

    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True, given=False)
    f = Symbol(shape=(oo,), real=True)
    g = Symbol(shape=(oo, oo), real=True)
    Eq << apply(Sum[i:m, j:n](f[i] * g[i, j]))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Algebra.Sum.eq.AddSumS, cond={n})

    s = Symbol(Sum[j:n + 1](f[i] * g[i, j]))
    Eq << s.this.definition

    Eq << Eq[-1].apply(Algebra.EqSumS.of.Eq, (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(Algebra.Sum.eq.AddSumS, cond={n})

    Eq << Eq[-1].this.rhs.args[1].apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.apply(Algebra.EqAddS.Is.Eq)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Eq_Ite.of.All_Imp.apply(Eq[-1], n=n, start=1)





if __name__ == '__main__':
    run()

# created on 2018-04-30
# updated on 2023-08-26
from . import intlimit
from . import subst
