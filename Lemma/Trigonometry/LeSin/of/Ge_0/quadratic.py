from util import *


@apply
def apply(le_zero):
    x = le_zero.of(Expr >= 0)
    return sin(x) <= x * (1 + x / S.Pi)

@prove
def prove(Eq):
    from Lemma import Calculus, Trigonometry, Set, Algebra, Logic

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    @Function
    def f(x):
        return x * (1 + x / S.Pi) - sin(x)
    Eq << f(x).this.defun()

    Eq << Calculus.EqGrad.of.Eq.apply(Eq[-1], (x,))

    Eq.eq_grad = Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Trigonometry.Cos.In.Icc.apply(x)

    Eq << -Set.Le.of.In_Icc.apply(Eq[-1])

    Eq << Eq[-1] + 1

    Eq << Eq[0] * 2 / S.Pi

    Eq << Eq[-1] + Eq[-2]

    Eq << Algebra.Ge.of.Eq.Ge.apply(Eq.eq_grad, Eq[-1])

    Eq << Logic.AllIn.of.All.apply(Eq[-1], (x, Interval(0, oo)))

    Eq << Calculus.All.Ge.of.All_Ge_0.monotony.right_open.apply(Eq[-1])

    Eq << Eq[-1].this.find(f).defun()

    Eq << Eq[-1].this.find(f).defun()

    Eq << Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])

    Eq << Algebra.Le.of.Ge_0.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-03
