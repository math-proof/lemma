from util import *


@apply
def apply(given):
    x, y = given.of(Mul <= 0)
    return Or(And(x >= 0, y <= 0), And(x <= 0, y >= 0))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x, y = Symbol(real=True, given=True)

    Eq << apply(x * y <= 0)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.args[0].apply(Bool.Or_AndNot.of.Or, pivot=1)

    Eq << Eq[-1].this.args[1].apply(Bool.Or_AndNot.of.Or, pivot=1)

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.args[1].apply(Bool.OrAndS.of.And_Or)

    Eq << Eq[-1].this.args[-1].apply(Algebra.Gt_0.of.Gt_0.Gt_0)

    Eq << Bool.BFn.of.BFnIte.Cond.apply(Eq[0], Eq[-1], invert=True)

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-1])

    Eq << Eq[-1].apply(Algebra.Gt_0.of.Lt_0.Lt_0)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2019-05-30
