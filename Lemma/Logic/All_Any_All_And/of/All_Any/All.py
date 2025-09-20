from util import *


@apply
def apply(all, all_any):
    from sympy.concrete.limits import limits_include, limits_difference
    fx, *limits_a = all.of(All)

    exists, *limits_b = all_any.of(All)
    assert limits_include(limits_a, limits_b)

    limits_a = limits_difference(limits_a, limits_b)

    assert limits_a
    fy, *limits_c = exists.of(Any)
    return All(Any(All(fx & fy, *limits_a), *limits_c), *limits_b)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(shape=(oo,), etype=dtype.integer)
    n, k = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    j = Symbol(domain=Range(k + 1))
    s = Symbol(etype=dtype.integer.set[k + 1])
    Eq << apply(All[i:Range(k + 1) - {j}, x[:k + 1]:s](Equal(x[i] & x[j], x[i].etype.emptySet)),
                All[x[:k + 1]:s](Any[j](Subset({n}, x[j]))))

    Eq << Eq[-1].this.expr.expr.apply(Logic.All.given.All_Or_Not)

    Eq << Eq[-1].this.expr.apply(Logic.Any_Or.given.OrAnyS, simplify=None)

    Eq << Eq[-1].this.find(Any).apply(Algebra.Any.given.Cond, simplify=None)

    Eq << Eq[-1].this.expr.apply(Logic.Or_Not.given.All)

    Eq << Eq[-1].this.expr.apply(Logic.Any_And.given.Any.All, index=0)

    Eq << Logic.All_And.given.All.All.apply(Eq[-1])




if __name__ == '__main__':
    run()

# created on 2018-12-03
# updated on 2023-05-12
