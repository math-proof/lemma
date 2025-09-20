from util import *


@apply
def apply(given, w):
    lhs, *limits = given.of(All[Equal[0]])
    factor = w[tuple(i for i, *_ in limits)]

    return Equal(Sum(lhs * factor, *limits), 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f = Function(shape=(), complex=True)
    w = Symbol(complex=True, shape=(oo,))
    Eq << apply(All[i:n](Equal(f(i), 0)), w=w)

    Eq << Eq[0].this.expr * w[i]

    Eq << Algebra.Sum.eq.Zero.of.All_Eq_0.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2019-01-24
