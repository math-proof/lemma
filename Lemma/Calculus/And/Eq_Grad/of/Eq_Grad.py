from util import *


@apply
def apply(eq_grad):
    (fx, (x, S[1])), y = eq_grad.of(Equal[Derivative])
    return Equal(Derivative[x + S.Infinitesimal](fx), y), Equal(Derivative[x - S.Infinitesimal](fx), y)


@prove
def prove(Eq):
    from Lemma import Calculus

    x, y = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(Derivative[x](f(x)), y))

    Eq << Eq[0].this.lhs.apply(Calculus.Grad.eq.Limit)

    Eq << Calculus.And.Eq_Limit.of.Eq_Limit.apply(Eq[-1])

    Eq << Eq[1].this.lhs.apply(Calculus.Grad.eq.Limit.one_sided)

    Eq << Eq[2].this.lhs.apply(Calculus.Grad.eq.Limit.one_sided)


if __name__ == '__main__':
    run()
# created on 2023-11-10
