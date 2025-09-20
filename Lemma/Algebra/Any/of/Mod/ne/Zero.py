from util import *


@apply
def apply(given, k=None):
    n = given.of(Unequal[Expr % 2, 0])
    if k is None:
        k = Symbol(integer=True)

    return Any[k](Equal(n, k * 2 + 1))


@prove
def prove(Eq):
    from Lemma import Algebra
#     n = q * d + r
    n = Symbol(integer=True, given=True)

    r = Symbol(integer=True)

    Eq << apply(Unequal(n % 2, 0))

    Eq << Algebra.Eq_odd.of.Ne_0.apply(Eq[0])

    Eq << Algebra.Any.of.Eq_odd.apply(Eq[-1], k=Eq[1].variable)


if __name__ == '__main__':
    run()
# created on 2019-05-10
