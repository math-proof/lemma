from util import *


@apply
def apply(x):
    return log(x) >= 1 - 1 / x


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Algebra.Log.le.Sub_1.apply(x)

    Eq << -Eq[-1]

    Eq << Eq[-1].subs(x, 1 / x)
    Eq << Eq[-1].this.find(Log).simplify()


if __name__ == '__main__':
    run()
# created on 2019-09-21
