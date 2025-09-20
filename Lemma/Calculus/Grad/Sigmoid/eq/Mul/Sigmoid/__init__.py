from util import *


@apply
def apply(self):
    fx, (x, S[1]) = self.of(Derivative[sigmoid])
    assert not x.shape
    return Equal(self, sigmoid(fx) * (1 - sigmoid(fx)) * Derivative[x](fx).doit())


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Derivative[x](sigmoid(f(x))))

    Eq << Eq[0].this.lhs.expr.defun()

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1].this.find(sigmoid).defun()

    Eq << Eq[-1].this.find(sigmoid).defun()

    Eq << Eq[-1] * (1 + exp(-f(x)))

    Eq << Eq[-1] * (1 + exp(-f(x)))

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)


if __name__ == '__main__':
    run()
# created on 2022-01-01


from . import vector
