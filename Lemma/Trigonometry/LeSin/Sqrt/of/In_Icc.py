from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    assert domain in Interval(0, S.Pi / 4)
    return sin(x) <= sqrt(2 * x / S.Pi)

@prove(proved=False)
def prove(Eq):
    from Lemma import Algebra, Calculus, Logic

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, S.Pi / 4)))

    @Function
    def f(t):
        return sqrt(2 * t / S.Pi) - sin(t)
    t, ξ = Symbol(real=True)
    Eq.ft = f(t).this.defun()

    Eq.xi = f(ξ).this.defun()

    Eq.All_Eq = All[ξ : Interval(0, S.Pi / 4)](Equal(Limit[t:ξ](f(t)), f(ξ)), plausible=True)

    Eq << Eq.All_Eq.subs(Eq.xi, Eq.ft)

    Eq << Eq[-1].this.find(Limit).doit()

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq.all_el = All[t:0:S.Pi / 4](Element(Derivative[t](f(t)), Interval(-oo, oo)), plausible=True)

    Eq << Eq.all_el.subs(Eq.ft)

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this().expr.simplify()

    Eq << Eq.ft.subs(t, 0)

    Eq << Eq.ft.subs(t, S.Pi / 4)

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])

    Eq << Calculus.Any.Eq.Rolle.of.IsContinuous.IsDifferentiable.Eq.apply(Eq.All_Eq, Eq.all_el, Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-03
# updated on 2023-10-15
