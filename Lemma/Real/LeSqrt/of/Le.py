from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Expr <= Expr)
    assert lhs >= 0
    return LessEqual(sqrt(lhs), sqrt(rhs))


@prove
def prove(Eq):
    from Lemma import Int, Bool

    x, y = Symbol(real=True)
    Eq << apply(LessEqual(x * x, y * y))

    Eq << Eq[0] - Eq[0].rhs

    Eq << Eq[-1].this.lhs.factor()

    Eq << Bool.Or.of.Le_0.split.Mul.apply(Eq[-1])

    Eq << Eq[-1].this.find(Add <= 0) - y

    Eq << Eq[-1].this.find(Add >= 0) + y

    Eq << Eq[-1].this.find(Add <= 0) + y

    Eq << Eq[-1].this.find(Add >= 0) - y

    Eq << Eq[-1].this.args[0].apply(Int.LeAbs.of.Le.Ge.both)

    Eq << Eq[-1].this.find(And).apply(Int.LeAbs.of.Le.Ge.both)





if __name__ == '__main__':
    run()

# created on 2019-05-31
# updated on 2023-05-14
