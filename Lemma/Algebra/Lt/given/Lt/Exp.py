from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Less)

    return Less(exp(lhs), exp(rhs))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply(Less(x, y))

    Eq << Algebra.LtLog.of.Lt.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2022-04-01
