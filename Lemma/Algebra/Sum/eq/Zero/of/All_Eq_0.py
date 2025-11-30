from util import *


@apply
def apply(given):
    lhs, *limits = given.of(All[Equal[0]])

    return Equal(Sum(lhs, *limits), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f = Function(complex=True)
    Eq << apply(All[i:n](Equal(f(i), 0)))

    Eq << Finset.Sum.of.All_Eq.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2019-01-24
