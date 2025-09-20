from util import *


@apply
def apply(greater_than, less_than):
    x, m = greater_than.of(GreaterEqual)
    S[x], M = less_than.of(LessEqual)

    return LessEqual(x * x, Max(m * m, M * M))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, m, M = Symbol(real=True, given=True)
    Eq << apply(x >= m, x <= M)

    Eq << Eq[-1].apply(Logic.Cond.given.Or.OrNot, cond=x >= 0)

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Eq[1].apply(Logic.AndOrS.of.Cond, cond=x >= 0)

    Eq << Logic.And_And.of.And.apply(Eq[-1])

    Eq << Logic.Or_AndNot.of.Or.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(Algebra.LeSquare.of.Ge_0.Le)

    Eq << Eq[-1].this.args[1].apply(Algebra.Le.of.Le.relax, Eq[2].rhs)

    Eq << Eq[0].apply(Logic.AndOrS.of.Cond, cond=x > 0)

    Eq << Logic.And_And.of.And.apply(Eq[-1])

    Eq << Logic.Or_AndNot.of.Or.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(Algebra.LeSquare.of.Le_0.Ge)

    Eq << Eq[-1].this.args[1].apply(Algebra.Le.of.Le.relax, Eq[2].rhs)

    Eq << Eq[-1].this.args[0].apply(Algebra.Ge.of.Gt.relax)





if __name__ == '__main__':
    run()
# created on 2019-10-25
# updated on 2023-05-13
