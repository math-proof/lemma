from util import *


@apply
def apply(el, all_le):
    lim, R = el.of(Element)
    fx, (x, x0) = lim.of(Limit)
    assert R in Reals
    S[fx], (x, cond) = all_le.of(All[Expr >= 0])
    diff, (delta, S[diff]) = cond.of((Abs > 0) & (Expr > Abs))
    S[x0] = x - diff
    assert delta > 0
    return lim >= 0


@prove
def prove(Eq):
    from Lemma import Calculus, Set

    x = Symbol(real=True)
    x0 = Symbol(real=True, given=True)
    delta = Symbol(real=True, given=True, positive=True)
    f = Function(real=True)
    Eq << apply(
        Element(Limit[x:x0](f(x)), Reals),
        All[x:(abs(x - x0) > 0) & (delta > abs(x - x0))](f(x) >= 0))

    @Function
    def g(x):
        return -f(x)
    Eq.g_def = g(x).this.defun()

    Eq << -Eq.g_def.reversed

    Eq <<= Eq[0].subs(Eq[-1]), Eq[1].subs(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(Calculus.Limit.eq.Mul), -Eq[-1].this.expr

    Eq << Set.Neg.In.IccNegS.of.In_Icc.apply(Eq[-2])

    Eq << Calculus.Le_0.Limit.of.IsReal.All_Le.apply(*Eq[-2:])

    Eq << Eq[-1].subs(Eq.g_def)

    Eq << -Eq[-1].this.lhs.apply(Calculus.Limit.eq.Mul)




if __name__ == '__main__':
    run()
# created on 2023-10-15

from . import one_sided
