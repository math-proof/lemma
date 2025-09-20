from util import *


@apply
def apply(given):
    from Lemma.Algebra.All.of.All.limits.merge import merge
    return merge(given)


@prove
def prove(Eq):
    from Lemma import Algebra
    n = Symbol(integer=True, positive=True)
    a, b = Symbol(real=True)

    x = Symbol(real=True, shape=(oo,))
    f = Function(real=True)

    Eq << apply(All[x[:n]:CartesianSpace(Interval(a, b), n), x[n]:Interval(a, b)](f(x[:n + 1]) > 0))

    Eq << Algebra.All.of.All.limits.split.apply(Eq[1], index=n)


if __name__ == '__main__':
    run()

# created on 2018-12-08
