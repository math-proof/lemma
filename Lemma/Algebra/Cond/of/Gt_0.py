from util import *


@apply
def apply(given):
    return given.of(Bool > 0)


@prove
def prove(Eq):
    from Lemma import Bool

    a, b = Symbol(real=True)
    Eq << apply(functions.Bool(a > b) > 0)

    Eq << Eq[0].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Bool.And.Imp.of.Cond_Ite.apply(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-11-05
