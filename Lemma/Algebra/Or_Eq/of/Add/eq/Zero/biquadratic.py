from util import *


@apply
def apply(fx, x=None):
    from Lemma.Algebra.And.Imp.of.Add.eq.Zero.quartic.one_leaded import quartic_coefficient
    fx = fx.of(Equal[0])
    S[1], S[0], alpha, S[0], gamma = quartic_coefficient(fx, x=x)
    delta = alpha ** 2 - 4 * gamma
    return Equal(x, sqrt(sqrt(delta) / 2 - alpha / 2)) | Equal(x, -sqrt(sqrt(delta) / 2 - alpha / 2)) | Equal(x, sqrt(-sqrt(delta) / 2 - alpha / 2)) | Equal(x, -sqrt(-sqrt(delta) / 2 - alpha / 2))


@prove
def prove(Eq):
    from Lemma import Algebra, Int, Int

    x, alpha, gamma = Symbol(complex=True, given=True)
    fx = x ** 4 + alpha * x ** 2 + gamma
    Eq << apply(Equal(fx, 0), x=x)

    y = Symbol(x ** 2)
    Eq << Eq[0].subs(y.this.definition.reversed)

    Eq << Algebra.And_Imp_Or_EqS_Div.of.Add.eq.Zero.quadratic.apply(Eq[-1], y)

    Eq << Eq[-1].subs(y.this.definition)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.args[-1].apply(Algebra.OrEqS_0.of.Eq_Square)

    Eq << Eq[-1].this.args[-1].apply(Algebra.OrEqS_0.of.Eq_Square)

    Eq << Eq[-1].this.args[-1].apply(Int.EqAdd.Is.Eq_Sub)

    Eq << Eq[-1].this.args[-1].apply(Int.EqAdd.Is.Eq_Sub)

    Eq << Eq[-1].this.args[-1].apply(Int.EqAdd.Is.Eq_Sub)

    Eq << Eq[-1].this.args[-1].apply(Int.EqAdd.Is.Eq_Sub)





if __name__ == '__main__':
    run()
# created on 2018-11-26
# updated on 2023-05-17
