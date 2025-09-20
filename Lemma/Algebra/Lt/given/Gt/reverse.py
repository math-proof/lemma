from util import *


@apply
def apply(lt):
    x, a = lt.of(Less)
    return Greater(a, x)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(x < a)

    Eq << Algebra.Lt.of.Gt.reverse.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2019-12-17
