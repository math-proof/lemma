from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    assert domain in Interval(0, S.Pi / 2)
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from Lemma import Calculus, Trigonometry, Algebra, Set, Logic

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, S.Pi / 2)))

    @Function
    def f(x):
        return sin(x) - x * (1 - x / S.Pi)
    Eq << f(x).this.defun()

    Eq << Calculus.EqGrad.of.Eq.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this.find(cos).apply(Trigonometry.Cos.eq.Sub.Square.Sin)

    Eq << Eq[-1] / 2

    Eq.eq_grad = Eq[-1].this.rhs.apply(Algebra.Sub.Square.eq.Mul)

    Eq << Set.InDiv.of.In_Icc.apply(Eq[0], 2)

    Eq <<= Trigonometry.Ge_0.Sin.of.In_Icc.apply(Eq[-1]), Trigonometry.LeSin.Sqrt.of.In_Icc.apply(Eq[-1])

    Eq << Algebra.Ge.of.Ge.Ge.apply(Eq[-2], Eq[-1])

    Eq <<= Algebra.Ge_0.Add.of.Ge_0.Ge_0.apply(Eq[-1], Eq[-3]), Algebra.Ge_0.of.Le.apply(Eq[-2])

    Eq <<= Algebra.Ge_0.of.Ge_0.Ge_0.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Ge.of.Eq.Ge.apply(Eq.eq_grad, Eq[-1]) * 2

    Eq << Logic.AllIn.of.All.apply(Eq[-1], (x, Interval(0, S.Pi / 2)))

    Eq << Calculus.All.Ge.of.All_Ge_0.monotony.right_close.apply(Eq[-1])

    Eq << Eq[-1].this.find(f).defun()

    Eq << Eq[-1].this.find(f).defun()

    Eq << Eq[-1].this.expr.apply(Algebra.Ge.of.Ge_0)

    Eq << Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-03
# updated on 2025-04-10
