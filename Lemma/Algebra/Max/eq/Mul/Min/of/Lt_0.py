from util import *


@apply
def apply(is_negative, self, div=False):
    factor = is_negative.of(Expr < 0)
    args = self.of(Max)

    if div:
        args = [arg * factor for arg in args]
        rhs = Min(*args) / factor
    else:
        args = [arg / factor for arg in args]
        rhs = Min(*args) * factor

    return Equal(self, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat

    x, y = Symbol(real=True)
    r = Symbol(real=True)
    Eq << apply(r < 0, Max(r * x, r * y))

    Eq << Eq[-1].this.lhs.apply(Nat.Max.eq.IteGe)

    Eq << Eq[-1].this.rhs.args[1].apply(Nat.Min.eq.IteLe)

    Eq << Eq[-1].this.lhs.apply(Nat.Ite_MulS.eq.Mul_Ite)

    Eq.eq = Algebra.Eq.given.Eq.Div.apply(Eq[-1], r)

    Eq.equivalent = Iff(Eq[-1].find(GreaterEqual), Eq[-1].rhs.find(LessEqual), plausible=True)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq.equivalent)

    Eq <<= Bool.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq[-2]), Algebra.Given.given.Given_And.apply(Eq[-1], cond=Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Algebra.LeDivS.of.Ge.Lt_0), Eq[-1].this.rhs.apply(Algebra.GeMul.of.Lt_0.Le)

    Eq << Algebra.Cond.given.Cond.subst.Cond.apply(Eq.eq, old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)





if __name__ == '__main__':
    run()
# created on 2020-01-19
# updated on 2021-10-02
