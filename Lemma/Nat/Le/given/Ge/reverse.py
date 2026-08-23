from util import *


@apply
def apply(ge):
    x, a = ge.of(LessEqual)
    return GreaterEqual(a, x)


@prove
def prove(Eq):
    from Lemma import Nat

    x, a = Symbol(real=True, given=True)
    Eq << apply(x <= a)

    Eq << Nat.Le.of.Ge.reverse.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2019-10-29
