from util import *


@apply
def apply(x, negate=False):
    if negate:
        x = -x
    return GreaterEqual(x, -abs(x))


@prove
def prove(Eq):
    from Lemma import Int

    x = Symbol(real=True, given=True)
    Eq << apply(x)

    Eq << -Eq[-1]

    Eq << Int.GeAbs.apply(-x)


if __name__ == '__main__':
    run()
# created on 2018-06-30
