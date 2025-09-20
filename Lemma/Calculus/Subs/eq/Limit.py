from util import *


@apply
def apply(self):
    (fx, (x, S[1])), [S[x], xi] = self.of(Subs[Derivative])

    return Equal(self, Limit[x:xi]((fx - fx._subs(x, xi)) / (x - xi)))


@prove
def prove(Eq):
    from Lemma import Calculus

    x, t = Symbol(real=True)
    x0 = Symbol(real=True, given=True)
    f = Function(real=True)
    Eq << apply(Subs[x:x0](Derivative(f(x), x)))

    Eq << Eq[0].this.rhs.apply(Calculus.Limit.limits.offset, x0)

    Eq << Derivative(f(t), t).this.apply(Calculus.Grad.eq.Limit)

    Eq << Eq[-1].this.rhs.apply(Calculus.Limit.limits.subst, x)
    Eq << Eq[-1].subs(t, x0)


if __name__ == '__main__':
    run()
# created on 2020-04-06
