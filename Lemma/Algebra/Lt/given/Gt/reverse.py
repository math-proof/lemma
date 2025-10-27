from util import *


@apply
def apply(lt):
    x, a = lt.of(Less)
    return Greater(a, x)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, a = Symbol(real=True, given=True)
    Eq << apply(x < a)

    Eq << Nat.Lt.of.Gt.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2019-12-17
