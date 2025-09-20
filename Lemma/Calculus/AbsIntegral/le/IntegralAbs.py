from util import *


@apply
def apply(self):
    expr, *limits = self.of(Integral)
    return Abs(self) <= Integral(Abs(expr), *limits)


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra

    a, b = Symbol(real=True)
    x = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Integral[x:a:b](f(x)))

    Eq << Calculus.Integral.le.Integral_Abs.apply(Eq[0].lhs.find(Integral))


    @Function
    def g(x):
        return -f(x)
    Eq << Calculus.Integral.le.Integral_Abs.apply(Eq[0].lhs.find(Integral)._subs(f(x), g(x)))
    Eq << Eq[-1].this.find(g).defun()
    Eq << -Eq[-1].this.find(g).defun()
    Eq << Algebra.LeAbs.of.Le.Ge.apply(Eq[1], Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-04-15
