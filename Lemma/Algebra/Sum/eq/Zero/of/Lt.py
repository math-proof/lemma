from util import *


@apply
def apply(le, sgm):
    b, a = le.of(Less)
    expr, (k, S[a], S[b]) = sgm.of(Sum)
    return Equal(sgm, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    a, b = Symbol(integer=True, given=True)
    n = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(b < a, Sum[n:a:b](f(n)))

    Eq << Nat.Le.of.Lt.apply(Eq[0])
    Eq << Algebra.Sum.eq.Zero.of.Le.apply(Eq[-1], Eq[1].lhs)


if __name__ == '__main__':
    run()
# created on 2020-01-04
