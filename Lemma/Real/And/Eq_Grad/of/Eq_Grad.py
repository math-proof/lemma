from util import *


@apply
def apply(eq_grad):
    (fx, (x, S[1])), y = eq_grad.of(Equal[Derivative])
    return Equal(Derivative[x + S.Infinitesimal](fx), y), Equal(Derivative[x - S.Infinitesimal](fx), y)


@prove
def prove(Eq):
    from Lemma import Real

    x, y = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(Derivative[x](f(x)), y))

    Eq << Eq[0].this.lhs.apply(Real.Grad.eq.Lim)

    Eq << Real.And.Eq_Lim.of.Eq_Lim.apply(Eq[-1])

    Eq << Eq[1].this.lhs.apply(Real.Grad.eq.Lim.one_sided)

    Eq << Eq[2].this.lhs.apply(Real.Grad.eq.Lim.one_sided)


if __name__ == '__main__':
    run()
# created on 2023-11-10
