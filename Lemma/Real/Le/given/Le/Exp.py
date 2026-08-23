from util import *


@apply
def apply(given):
    lhs, rhs = given.of(LessEqual)

    return LessEqual(exp(lhs), exp(rhs))


@prove
def prove(Eq):
    from Lemma import Real

    x, y = Symbol(real=True)
    Eq << apply(LessEqual(x, y))

    Eq << Real.LeLog.of.Le.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2022-03-31
