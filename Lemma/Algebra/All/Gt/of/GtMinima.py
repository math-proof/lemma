from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Greater[Minima])
    return All(fx > M, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, t = Symbol(real=True)
    M = Symbol(real=True, given=True)
    f = Function(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(Minima[x:S](f(x)) > M)

    @Function
    def g(x):
        return -f(x)
    Eq.g_def = g(x).this.defun()

    Eq << -Eq.g_def.reversed

    Eq << Eq[0].subs(Eq[-1])

    Eq << -Eq[-1].this.lhs.apply(Algebra.Minima.eq.Neg.Maxima)

    Eq << Algebra.All.Lt.of.LtMaxima.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.g_def)

    Eq << -Eq[-1].this.expr


if __name__ == '__main__':
    run()
# created on 2023-11-12
