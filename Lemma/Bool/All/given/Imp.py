from util import *



@apply
def apply(given):
    expr, *limits = given.of(All)
    return Imply(given.limits_cond.simplify(), expr)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(All[n:Equal(f[n], g[n])](Equal(f[n + 1], g[n + 1])))

    Eq << Eq[1].this.apply(Bool.Imp.Is.All, wrt=n)


if __name__ == '__main__':
    run()
# created on 2018-12-07
