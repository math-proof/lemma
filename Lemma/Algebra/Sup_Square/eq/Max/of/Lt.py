from util import *


@apply
def apply(lt, left_open=True, right_open=True, x=None):
    m, M = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    self = Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, Max(m ** 2, M ** 2))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, x=x)

    Eq << Algebra.Eq.given.And.squeeze.apply(Eq[-1])

    Eq << Element(x, Interval(m, M, left_open=True, right_open=True)).this.apply(Set.LtSquare.of.In_Icc)

    Eq << Bool.All.of.Imp.apply(Eq[-1])

    Eq << Algebra.LeSup.of.All_Lt.apply(Eq[-1])

    Eq << Algebra.GeSup.given.All_Any_Gt.apply(Eq[3], 'U')

    Eq << Bool.All.given.Imp.apply(Eq[-1])

    Eq << Bool.Imp_And.of.Cond.apply(Eq[0], cond=Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.GtSquare.of.Lt.Lt_Max)


if __name__ == '__main__':
    run()
# created on 2019-09-08
