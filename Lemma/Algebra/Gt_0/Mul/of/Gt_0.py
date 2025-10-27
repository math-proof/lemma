from util import *


@apply
def apply(given, factor):
    assert factor > 0
    x = given.of(Expr > 0)

    return Greater(x * factor, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    h = Symbol(real=True, shape=(n,))
    a = Symbol(real=True, positive=True)
    Eq << apply(h[k] > 0, a)

    Eq << Greater(a, 0, plausible=True)

    Eq << Nat.Gt_0.of.Gt_0.Gt_0.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-08-21
