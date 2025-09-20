from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Less)
    assert lhs > 0

    return Less(log(lhs), log(rhs))


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(positive=True)
    y = Symbol(real=True)
    Eq << apply(Less(x, y))

    Eq << Algebra.GtLog.of.Gt.apply(Eq[0].reversed).reversed


if __name__ == '__main__':
    run()
# created on 2022-04-01
