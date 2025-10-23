from util import *


@apply
def apply(given, factor):
    assert factor < 0
    x = given.of(Expr > 0)

    return Less(x * factor, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Int

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    h = Symbol(real=True, shape=(n,))
    a = Symbol(real=True, negative=True)
    Eq << apply(h[k] > 0, a)

    Eq << Less(a, 0, plausible=True)

    Eq << Int.Lt_0.of.Gt_0.Lt_0.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-22
