from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    assert domain in Interval.open(0, S.Pi)
    return x + sin(x) > x ** 2 * cot(x / 2)

@prove
def prove(Eq):
    from Lemma import Calculus, Trigonometry, Algebra, Set, Logic

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval.open(0, S.Pi)))

    @Function(real=True)
    def f(x):
        return x + sin(x) - x ** 2 * cot(x / 2)
    Eq << f(x).this.defun()

    Eq << Calculus.EqGrad.of.Eq.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this.find(cot ** 2).apply(Trigonometry.Square.Cot.eq.Sub.Square.Csc)

    Eq << Eq[-1].this.find(csc).apply(Trigonometry.Csc.eq.Inv.Sin)

    Eq << Eq[-1].this.find(cos).apply(Trigonometry.Cos.eq.Sub.double)

    Eq.eq_grad = Eq[-1].this.find(cot).apply(Trigonometry.Cot.eq.Div)

    t = Symbol(real=True)
    args = Eq.eq_grad.rhs.args
    y = args[0] + args[1] / x ** 2 * t ** 2 + args[2] / x * t + args[3] + args[4]
    Eq << Algebra.Add.eq.Add.square_completing.apply(y)

    Eq << Eq[-1].this.rhs.find(cos ** 2).apply(Trigonometry.Square.Cos.eq.Sub.Square.Sin)

    Eq << Eq[-1].subs(t, x)

    Eq << sin(x).this.apply(Trigonometry.Sin.eq.Mul.double)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.eq_grad = Logic.Eq.of.Eq.Eq.apply(Eq.eq_grad, Eq[-1])

    Eq << Algebra.Ne_0.of.Div1.gt.Zero.apply(Eq.eq_grad)

    Eq << Algebra.Square.gt.Zero.of.Ne_0.apply(Eq[-1])

    Eq << Set.Gt.of.In_Icc.apply(Eq[0])

    Eq << Trigonometry.LtSin.of.Gt_0.apply(Eq[-1])

    Eq << Algebra.Gt_0.of.Lt.apply(Eq[-1])

    Eq << Algebra.Gt_0.Square.of.Gt_0.apply(Eq[-1])

    Eq << Algebra.Gt_0.Div.of.Gt_0.Gt_0.apply(Eq[-1], Eq[-5]) / 2

    Eq << Algebra.Gt.of.Eq.Gt.apply(Eq[-1], Eq.eq_grad)

    Eq << Logic.AllIn.of.All.apply(Eq[-1], (x, Interval(0, S.Pi, right_open=True)))

    Eq << Calculus.All.Gt.of.All_Gt_0.monotony.right_open.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[2])

    print('logic error here:', f(0), 'is not defined at 0')
    Eq << Eq[-1].this.find(f).defun()

    Eq << Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])

    Eq << Algebra.Gt.of.Sub.gt.Zero.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-03
