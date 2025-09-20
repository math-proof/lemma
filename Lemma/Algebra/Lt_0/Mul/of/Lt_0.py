from util import *


@apply
def apply(given, factor):
    assert factor > 0
    x = given.of(Expr < 0)

    return Less(x * factor, 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    h = Symbol(real=True, shape=(n,))
    a = Symbol(real=True, positive=True)
    Eq << apply(h[k] < 0, a)

    Eq << Greater(a, 0, plausible=True)

    Eq << Algebra.Lt_0.of.Gt_0.Lt_0.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2020-01-21
