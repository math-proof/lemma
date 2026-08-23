from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Greater)

    return Greater(exp(lhs), exp(rhs))


@prove
def prove(Eq):
    from Lemma import Real

    x, y = Symbol(real=True)
    Eq << apply(Greater(x, y))

    Eq << Real.GtLog.of.Gt.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2022-03-31
