from util import *


@apply
def apply(given):
    x, y = given.of(Mul > 0)
    return Or((x < 0) & (y < 0), (x > 0) & (y > 0))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y = Symbol(real=True, given=True)
    Eq << apply(x * y > 0)

    Eq << ~Eq[-1]

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.args[1].apply(Bool.OrAndS.of.And_Or)

    Eq << Eq[-1].this.find(And[Or]).apply(Bool.OrAndS.of.And_Or)

    Eq << Eq[-1].this.find((Expr <= 0) & (Expr >= 0)).apply(Algebra.Mul.le.Zero.of.Le_0.Ge_0)

    Eq << Eq[-1].this.find((Expr <= 0) & (Expr >= 0)).apply(Algebra.Le_0.of.Ge_0.Le_0)

    Eq << Eq[-1].this.args[0] * y

    Eq << Eq[-1].this.args[0] * x

    Eq <<= Eq[-1] & Eq[0]





if __name__ == '__main__':
    run()

# created on 2018-02-11

# updated on 2023-05-13

