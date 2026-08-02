from util import *


@apply
def apply(ge, le):
    x, y = le.of(LessEqual)
    S[x], S[-y] = ge.of(GreaterEqual)
    return LessEqual(abs(x), y)


@prove
def prove(Eq):
    from Lemma import Algebra, Int

    y, x = Symbol(real=True)
    Eq << apply(x >= -y, x <= y)

    Eq << Int.LeAbs.of.LeNeg.Le.apply(Eq[1], Eq[0])




if __name__ == '__main__':
    run()
# created on 2023-04-15
