from util import *


@apply
def apply(is_nonnegative, self, offset):
    expr = is_nonnegative.of(Expr >= 0)
    S[expr], (x, *ab) = self.of(Integral)
    if ab:
        a, b = ab
        limit = (x, a - offset, b - offset)
    else:
        limit = (x,)

    return Equal(self, Integral(expr._subs(x, x + offset), limit))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Bool

    x, a, b, d = Symbol(real=True)
    f = Function(real=True, integrable=True)
    Eq << apply(f(x) >= 0, Integral[x:a:b](f(x)), d)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=a > b)

    Eq <<= Eq[-2].this.find(Integral).apply(Calculus.Integral.eq.Ite), Eq[-1].this.find(Integral).apply(Calculus.Integral.eq.Ite)

    Eq <<= Eq[-2].this.find(Equal[~Integral]).apply(Calculus.Integral.eq.Ite), Eq[-1].this.find(Equal[~Integral]).apply(Calculus.Integral.eq.Ite)

    Eq <<= Bool.Imp.given.Imp.subst.Bool.apply(Eq[-2]), Bool.Imp.given.Imp.subst.Bool.apply(Eq[-1], invert=True)

    Eq << -Eq[-2].this.rhs

    Eq << Bool.And.Imp.of.Cond.split.apply(Eq[0], cond=a > b)

    Eq << Eq[-2].this.rhs.apply(Calculus.EqIntegral.of.Ge_0.limits.offset.Icc, Eq[-3].find(Integral), d)

    Eq << Eq[-1].this.rhs.apply(Calculus.EqIntegral.of.Ge_0.limits.offset.Icc, Eq[-4].find(Integral), d)


if __name__ == '__main__':
    run()
# created on 2020-05-25


from . import Icc
