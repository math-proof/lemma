from util import *


@apply
def apply(given):
    x, y = given.of(LessEqual)
    return LessEqual(Ceil(x), Ceil(y))


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << ~Eq[1]

    Eq << Nat.Ge_Add_1.of.Gt.apply(Eq[-1]) - 1

    Eq << Algebra.Gt_Sub_.Ceil.One.apply(x)

    Eq << Algebra.Gt.of.Gt.Ge.apply(Eq[-2], Eq[-1])

    Eq << Algebra.GeCeil.apply(y)

    Eq << Algebra.Gt.of.Gt.Ge.apply(Eq[-2], Eq[-1])

    Eq <<= Eq[-1] & Eq[0]



if __name__ == '__main__':
    run()
# created on 2021-12-27
# updated on 2021-12-27
