from util import *


@apply
def apply(lt):
    lhs, rhs = lt.of(Less)
    return log(lhs) < log(rhs)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Less(x, y))

    Eq << Algebra.LtExp.of.Lt.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-04-16
