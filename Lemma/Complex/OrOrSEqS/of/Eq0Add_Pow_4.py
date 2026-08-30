from util import *


@apply
def apply(fx, x=None):
    from Lemma.Complex.Imp_OrOrSEqS_Sub.Imp_OrOrSEqS_SubDiv_2.of.Eq0Add_Pow_4 import quartic_coefficient
    fx = fx.of(Equal[0])
    S[1], S[0], alpha, S[0], gamma = quartic_coefficient(fx, x=x)
    delta = alpha ** 2 - 4 * gamma
    return Equal(x, sqrt((sqrt(delta) - alpha) / 2)) | Equal(x, -sqrt((sqrt(delta) - alpha) / 2)) | Equal(x, sqrt((-sqrt(delta) - alpha) / 2)) | Equal(x, -sqrt((-sqrt(delta) - alpha) / 2))


@prove
def prove(Eq):
    from Lemma import Int, Nat, Complex

    x, alpha, gamma = Symbol(complex=True, given=True)
    fx = x ** 4 + alpha * x ** 2 + gamma
    Eq << apply(Equal(fx, 0), x=x)

    y = Symbol(x ** 2)
    Eq << Eq[0].subs(y.this.definition.reversed)

    Eq << Complex.OrEqS_Div.of.Eq0Add_Mul_Square.Ne_0.apply(Unequal(1, 0, evaluate=False), Eq[-1], x=y)

    Eq << Eq[-1].subs(y.this.definition)

    Eq << Eq[-1].this.find(Mul).apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.args[-1].apply(Int.OrEqS_0.of.Square)

    Eq << Eq[-1].this.args[-1].apply(Int.OrEqS_0.of.Square)

    Eq << Eq[-1].this.args[-1].apply(Int.EqAdd.Is.Eq_Sub)

    Eq << Eq[-1].this.args[-1].apply(Int.EqAdd.Is.Eq_Sub)

    Eq << Eq[-1].this.args[-1].apply(Int.EqAdd.Is.Eq_Sub)

    Eq << Eq[-1].this.args[-1].apply(Int.EqAdd.Is.Eq_Sub)

    Eq << Eq[-1].this.args[1].rhs.together()

    Eq << Eq[-1].this.args[-1].rhs.together()


if __name__ == '__main__':
    run()
# created on 2018-11-26
# updated on 2026-08-30
