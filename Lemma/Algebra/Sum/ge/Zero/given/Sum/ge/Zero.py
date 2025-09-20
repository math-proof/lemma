from util import *


@apply
def apply(given, index=0):
    function, *limits = given.of(Sum >= 0)
    del limits[index]
    return GreaterEqual(Sum(function, *limits), 0)


@prove
def prove(Eq):
    from Lemma import Algebra
    f = Function(real=True)
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    Eq << apply(Sum[i:n, j:n](f(i, j)) >= 0)

    Eq << Algebra.GeSum.of.Ge.apply(Eq[1], (i, 0, n))

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.swap)


if __name__ == '__main__':
    run()
# created on 2020-03-26
