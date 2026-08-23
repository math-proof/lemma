from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    assert domain in Interval(0, S.Pi / 2)
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from Lemma import Real, Set, Bool, Nat, Int

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, S.Pi / 2)))

    @Function
    def f(x):
        return sin(x) - x * (1 - x / S.Pi)
    Eq << f(x).this.defun()

    Eq << Real.EqGrad.of.Eq.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.apply(Real.Grad.eq.Add)

    Eq << Eq[-1].this.find(cos).apply(Real.Cos.eq.Sub.Square.Sin)

    Eq << Eq[-1] / 2

    Eq.eq_grad = Eq[-1].this.rhs.apply(Int.Sub.Square.eq.Mul)

    Eq << Set.InDiv.of.In_Icc.apply(Eq[0], 2)

    Eq <<= Real.Ge_0.Sin.of.In_Icc.apply(Eq[-1]), Real.LeSin.Sqrt.of.In_Icc.apply(Eq[-1])

    Eq << Nat.Ge.of.Ge.Ge.apply(Eq[-2], Eq[-1])

    Eq <<= Nat.Le0Add.of.Ge_0.Ge_0.apply(Eq[-1], Eq[-3]), Nat.Ge_0.of.Le.apply(Eq[-2])

    Eq <<= Int.Le0Mul.of.Ge_0.Ge_0.apply(Eq[-1], Eq[-2])

    Eq << Nat.Ge.of.Eq.Ge.apply(Eq.eq_grad, Eq[-1]) * 2

    Eq << Bool.AllIn.of.All.apply(Eq[-1], (x, Interval(0, S.Pi / 2)))

    Eq << Real.All.Ge.of.All_Ge_0.monotony.right_close.apply(Eq[-1])

    Eq << Eq[-1].this.find(f).defun()

    Eq << Eq[-1].this.find(f).defun()

    Eq << Eq[-1].this.expr.apply(Nat.Ge.of.Ge_0)

    Eq << Bool.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-03
# updated on 2025-04-10
