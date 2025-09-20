from util import *


@apply
def apply(given):
    a, b = given.of(Less)
    return Subset({b, a}, Interval(a, b))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x, y = Symbol(real=True, given=True)
    Eq << apply(x < y)

    Eq << Algebra.Le.of.Lt.apply(Eq[0])

    Eq << Set.Subset.Finset.of.Le.apply(Eq[-1], simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-10-22
