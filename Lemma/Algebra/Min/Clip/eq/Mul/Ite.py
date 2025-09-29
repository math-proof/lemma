from util import *


@apply
def apply(self):
    (A, r), ((S[r], epsilon_less, epsilon_more), S[A]) = self.of(Min[Mul, Mul[clip]])
    ε = (epsilon_more - epsilon_less) / 2
    assert epsilon_more + epsilon_less == 2
    assert 0 < ε < 1
    return Equal(self, A * Piecewise((Piecewise((1 + ε, r > 1 + ε), (r, True)), A >= 0), (Piecewise((1 - ε, r <= 1 - ε), (r, True)), True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    ε = Symbol(domain=Interval(0, 1, left_open=True, right_open=True))
    # 0 < ε < 1
    r_t = Symbol(real=True, positive=True)
    A_t = Symbol(real=True)
    Eq << apply(Min(r_t * A_t, clip(r_t, 1 - ε, 1 + ε) * A_t))

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[0], cond=Eq[-1].find(GreaterEqual))

    Eq <<= Logic.Imp.given.Imp.subst.Bool.apply(Eq[-2]), Logic.Imp.given.Imp.subst.Bool.apply(Eq[-1], invert=True)

    Eq << Logic.Imp.given.And.Imp.split.apply(Eq[-2], cond=A_t > 0)

    Eq << Logic.Imp.given.Imp.subst.apply(Eq[-1])

    Eq <<= Logic.Imp.given.Imp_And.apply(Eq[-3]), Logic.Imp.given.Imp_And.apply(Eq[-2])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Lt_0.Eq.given.And.Div), Eq[-1].this.rhs.apply(Algebra.Gt_0.Eq.given.And.Div)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.EqAbs.of.Lt_0), Eq[-1].this.lhs.apply(Algebra.EqAbs.of.Gt_0)

    Eq <<= -Eq[-2].this.lhs, Eq[-1].this.lhs.reversed

    Eq << Eq[-2].this.lhs.reversed

    Eq <<= Logic.Imp.given.Imp.subst.apply(Eq[-2]), Logic.Imp.given.Imp.subst.apply(Eq[-1])

    Eq <<= Eq[-2].this.find(Min).apply(Algebra.Min.eq.Mul), Eq[-1].this.find(Min).apply(Algebra.Min.eq.Mul.Max)

    Eq <<= Eq[-2].this.find(clip).defun(), Eq[-1].this.find(clip).defun()

    Eq <<= Eq[-2].this.find(Piecewise).apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite), Eq[-1].this.find(Piecewise).apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Eq[-2].this.find(Min).apply(Algebra.Min.eq.IteLe)

    Eq << Eq[-1].this.find(Max).apply(Algebra.Max.eq.Ite.Gt)





if __name__ == '__main__':
    run()
# created on 2023-03-26
# updated on 2023-05-18
