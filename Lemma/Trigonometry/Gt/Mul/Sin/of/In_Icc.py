from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    assert domain in Interval.open(0, S.Pi)
    return x ** 2 * (x + sin(x)) / (x - sin(x)) > S.Pi ** 2

@prove(proved=False)
def prove(Eq):
    from Lemma import Calculus, Algebra, Trigonometry

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval.open(0, S.Pi)))

    @Function(real=True)
    def g(x):
        return x ** 2 * (x + sin(x)) / (x - sin(x))
    Eq << g(x).this.defun()

    Eq << Calculus.EqGrad.of.Eq.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.Mul.eq.Add)

    Eq << Eq[-1].this.rhs.find(Derivative).doit()

    Eq << Eq[-1].this.rhs.find(Derivative).doit()

    Eq << Eq[-1].this.rhs.find(Derivative).doit()

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul)

    Eq << Eq[-1].this.rhs.args[2].apply(Algebra.Add.eq.Mul.together)

    Eq << Eq[-1].this.rhs.args[2].expand()

    # Eq << Eq[-1].this.rhs.args[2].apply(Algebra.Add.eq.Mul)
    @Function(real=True)
    def h(x):
        return x ** 2 * (cos(x) + 1) - sin(x) * (x + sin(x))
    Eq << h(x).this.defun()

    Eq << Calculus.EqGrad.of.Eq.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this.rhs.expand()

    Eq << Trigonometry.Mul_.Csc.Sin.eq.One.apply(x) * (2 * x)

    Eq << Trigonometry.Cos.eq.Mul_.Sin.Cot.apply(x) * x

    Eq << Eq[-3].subs(Eq[-2].reversed, Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul)

    # https://www.zhihu.com/question/355479801



if __name__ == '__main__':
    run()
# created on 2023-10-03
