from util import *


@apply
def apply(lt):
    x, a = lt.of(Less)
    return Greater(a, x)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, a = Symbol(real=True, given=True)
    Eq << apply(x < a)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])




if __name__ == '__main__':
    run()
# created on 2020-01-10
