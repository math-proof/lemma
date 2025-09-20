from util import *


@apply
def apply(given):
    return given.of(Bool > 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, b = Symbol(real=True)
    Eq << apply(Bool(a > b) > 0)

    Eq << Eq[0].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Logic.Cond_Ite.given.And.Imp.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-11-05
