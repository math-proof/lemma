from util import *


@apply
def apply(given, *, simplify=True):
    fn1, *limits = given.of(All)
    cond = given.limits_cond
    if simplify:
        cond = cond.simplify()
    return Imply(cond, fn1)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(All[n:Equal(f[n], g[n])](Equal(f[n + 1], g[n + 1])))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Logic.Imp.of.AllSetOf)

    Eq << Eq[-1].this.rhs.apply(Logic.All.given.Imp)


if __name__ == '__main__':
    run()
# created on 2018-12-22
