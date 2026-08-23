from util import *


@apply
def apply(gt_zero):
    x = gt_zero.of(Expr >= 0)
    return sin(x) <= x

@prove
def prove(Eq):
    from Lemma import Real, Set, Bool, Nat

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    @Function(real=True)
    def f(x):
        return x - sin(x)
    Eq << f(x).this.defun()

    Eq << Real.EqGrad.of.Eq.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.apply(Real.Grad.eq.Add)

    Eq << Real.Cos.In.Icc.apply(x)

    Eq << Set.Le.of.In_Icc.apply(Eq[-1])

    Eq << Nat.Ge_0.of.Le.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-4].reversed)

    Eq << Bool.AllIn.of.All.apply(Eq[-1], (x, Interval(0, oo)))

    Eq << Real.All.Ge.of.All_Ge_0.monotony.right_open.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[2])

    Eq << Eq[-1].this.find(f).defun()

    Eq << Bool.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Nat.Le.of.Ge_0)

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-10-03

from . import quadratic
