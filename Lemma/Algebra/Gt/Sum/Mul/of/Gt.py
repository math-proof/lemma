from util import *


@apply
def apply(given, limit):
    lhs, rhs = given.of(Greater)

    n, a, b = limit

    assert n.is_integer
    assert b - 1 > a >= 0 or b > a > 0

    return Greater(Sum(n * lhs, limit).simplify(), Sum(n * rhs, limit).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)

    f, g = Function(shape=(), real=True)

    Eq << apply(Greater(f(i), g(i)), (i, 0, n + 1))

    k = Symbol(domain=Range(1, n + 1))

    Eq << Eq[0].subs(i, k)

    Eq << Eq[-1] * k

    Eq << Eq[-1].apply(Algebra.GtSum.of.Gt, (k,))

    Eq << Eq[-1].this.lhs.limits_subs(k, i)

    Eq << Eq[-1].this.rhs.limits_subs(k, i)


if __name__ == '__main__':
    run()

# created on 2019-07-25
