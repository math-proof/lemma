from util import *


@apply
def apply(self):
    fx, (x, S[1]) = self.of(Derivative[sigmoid])
    n, = x.shape
    return Equal(self, (sigmoid(fx) * (1 - sigmoid(fx)) * Ones(n, n)).T * Derivative[x](fx).doit())


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    f = Function(real=True)
    Eq << apply(Derivative[x](sigmoid(f(x))))

    Eq << Eq[0].this.lhs.expr.defun()

    Eq << sigmoid(f(x)).this.defun()

    Eq << (1 - sigmoid(f(x))).this.find(sigmoid).defun()

    Eq << Eq[-1] * Eq[-2]

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Add).apply(Algebra.Add.eq.Mul.together)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Mul(*Eq[-1].lhs.args[1:]).this.apply(Algebra.Mul.eq.Transpose)

    Eq << Eq[-1].this.rhs.apply(Algebra.Transpose.eq.Mul)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Mul(*Eq[-1].lhs.args[1:]).this.apply(Algebra.Mul.eq.Transpose)

    Eq << Eq[-2].subs(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-01
# updated on 2023-05-13


from . import using
