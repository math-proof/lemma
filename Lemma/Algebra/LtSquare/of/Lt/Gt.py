from util import *


@apply
def apply(lt, gt):
    x, m = gt.of(Greater)
    S[x], M = lt.of(Less)

    return Less(x * x, Max(m * m, M * M))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, m, M = Symbol(real=True, given=True)
    Eq << apply(x < M, x > m)

    Eq << Eq[-1].apply(Bool.Cond.given.Or.OrNot, cond=x >= 0)

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Eq[0].apply(Bool.AndOrS.of.Cond, cond=x >= 0)

    Eq << Bool.And_And.of.And.apply(Eq[-1])

    Eq << Bool.Or_AndNot.of.Or.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(Algebra.LtSquare.of.Ge_0.Lt)

    Eq << Eq[-1].this.args[1].apply(Algebra.Lt.of.Lt.relax, Eq[2].rhs)

    Eq << Eq[1].apply(Bool.AndOrS.of.Cond, cond=x > 0)

    Eq << Bool.And_And.of.And.apply(Eq[-1])

    Eq << Bool.Or_AndNot.of.Or.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(Algebra.LtSquare.of.Le_0.Gt)

    Eq << Eq[-1].this.find(Less).apply(Algebra.Lt.of.Lt.relax, Eq[2].rhs)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Ge.of.Gt.relax)





if __name__ == '__main__':
    run()
# created on 2019-08-31
# updated on 2023-05-20
