from util import *


@apply
def apply(given, num=1, evaluate=False):
    x = given.of(Expr < 0)
    assert num > 0
    return Less(num / x, 0, evaluate=evaluate)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True, given=True)
    d = Symbol(real=True, positive=True)
    Eq << apply(x < 0, num=d)

    Eq << Eq[-1] / d

    Eq << -Eq[0]

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[-1])
    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-05-20
