from util import *


@apply
def apply(given, factor):
    assert factor >= 0
    x = given.of(Expr >= 0)

    return GreaterEqual(x * factor, 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    h = Symbol(real=True, shape=(n,))
    a = Symbol(real=True, nonnegative=True)
    Eq << apply(h[k] >= 0, a)

    Eq << GreaterEqual(a, 0, plausible=True)
    Eq << Algebra.Ge_0.of.Ge_0.Ge_0.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-06-15
