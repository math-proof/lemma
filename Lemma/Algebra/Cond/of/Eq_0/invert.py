from util import *


@apply
def apply(given):
    cond, S[0] = given.of(Equal[Bool])
    return cond.invert()


@prove
def prove(Eq):
    from Lemma import Bool

    a, b = Symbol(real=True)
    Eq << apply(Equal((a > b).toNat, 0))

    Eq << Eq[0].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)




if __name__ == '__main__':
    run()
# created on 2023-11-05
