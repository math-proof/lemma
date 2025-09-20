from util import *


@apply
def apply(is_positive, self):
    factor = is_positive.of(Expr > 0)
    args = self.of(Min)

    args = [arg * factor for arg in args]
    return Equal(Min(*args), self * factor)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y = Symbol(real=True)
    r = Symbol(real=True)
    Eq << apply(r > 0, Min(x, y))

    Eq << Eq[-1].this.lhs.apply(Algebra.Min.eq.IteLe)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Min.eq.IteLe)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ite.eq.Mul)

    Eq.eq = Algebra.Eq.given.Eq.Div.apply(Eq[-1], r)

    Eq.equivalent = Iff(Eq[-1].find(LessEqual), Eq[-1].rhs.find(LessEqual), plausible=True)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq.equivalent)

    Eq <<= Logic.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq[-2]), Algebra.Given.given.Given_And.apply(Eq[-1], cond=Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Algebra.LeDiv.of.Gt_0.Le), Eq[-1].this.rhs.apply(Algebra.LeMul.of.Gt_0.Le)

    Eq << Algebra.Cond.given.Cond.subst.Cond.apply(Eq.eq, old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)


if __name__ == '__main__':
    run()
# created on 2019-08-16
