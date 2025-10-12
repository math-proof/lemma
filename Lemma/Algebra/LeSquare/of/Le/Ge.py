from util import *


@apply
def apply(greater_than, less_than):
    x, m = greater_than.of(GreaterEqual)
    S[x], M = less_than.of(LessEqual)

    return LessEqual(x * x, Max(m * m, M * M))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat

    x, m, M = Symbol(real=True, given=True)
    Eq << apply(x >= m, x <= M)

    Eq << Eq[-1].apply(Bool.Cond.given.Or.OrNot, cond=x >= 0)

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Eq[1].apply(Bool.AndOrS.of.Cond, cond=x >= 0)

    Eq << Bool.And_And.of.And.apply(Eq[-1])

    Eq << Bool.Or_AndNot.of.Or.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(Algebra.LeSquare.of.Ge_0.Le)

    Eq << Eq[-1].this.args[1].apply(Algebra.Le.of.Le.relax, Eq[2].rhs)

    Eq << Eq[0].apply(Bool.AndOrS.of.Cond, cond=x > 0)

    Eq << Bool.And_And.of.And.apply(Eq[-1])

    Eq << Bool.Or_AndNot.of.Or.apply(Eq[-2])

    Eq << Eq[-1].this.find(And).apply(Algebra.LeSquare.of.Le_0.Ge)

    Eq << Eq[-1].this.args[1].apply(Algebra.Le.of.Le.relax, Eq[2].rhs)

    Eq << Eq[-1].this.args[0].apply(Nat.Ge.of.Gt)





if __name__ == '__main__':
    run()
# created on 2019-10-25
# updated on 2023-05-13
