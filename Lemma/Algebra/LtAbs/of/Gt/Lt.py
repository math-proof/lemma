from util import *


@apply
def apply(gt, lt):
    x, y = lt.of(Less)
    S[x], S[-y] = gt.of(Greater)
    return Less(abs(x), y)


@prove
def prove(Eq):
    from Lemma import Algebra

    y, x = Symbol(real=True)
    Eq << apply(x > -y, x < y)

    Eq << Algebra.LtAbs.of.Lt.Gt.apply(Eq[1], Eq[0])




if __name__ == '__main__':
    run()
# created on 2023-04-15
