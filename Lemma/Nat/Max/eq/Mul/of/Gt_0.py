from util import *


@apply
def apply(is_positive, self):
    factor = is_positive.of(Expr > 0)
    args = self.of(Max)

    args = [arg * factor for arg in args]
    return Equal(Max(*args), self * factor)


@prove
def prove(Eq):
    from Lemma import Bool, Nat, Rat

    x, y = Symbol(real=True)
    r = Symbol(real=True)
    Eq << apply(r > 0, Max(x, y))

    Eq << Eq[-1].this.lhs.apply(Nat.Max.eq.IteGe)

    Eq << Eq[-1].this.rhs.args[1].apply(Nat.Max.eq.IteGe)

    Eq << Eq[-1].this.lhs.apply(Nat.Ite_MulS.eq.Mul_Ite)

    Eq.eq = Nat.Div.given.Eq.apply(Eq[-1], r)

    Eq.equivalent = Iff(Eq[-1].find(GreaterEqual), Eq[-1].rhs.find(GreaterEqual), plausible=True)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq.equivalent)

    Eq <<= Bool.And_Imp.given.And_ImpAnd.apply(Eq[0], Eq[-2]), Bool.Given.given.Given_And.apply(Eq[-1], cond=Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Rat.GeDivS.of.Ge.Gt_0), Eq[-1].this.rhs.apply(Nat.GeMulS.of.Ge.Gt_0)

    Eq << Bool.UFnIte.given.UFnIte.Iff.apply(Eq.eq, old=Eq.equivalent.lhs, new=Eq.equivalent.rhs)


if __name__ == '__main__':
    run()
# created on 2019-08-16
