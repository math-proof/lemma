from util import *


@apply
def apply(self, strict=False):
    if strict:
        cond = self > 0
    else:
        cond = self >= 0
    return Equal(self, Piecewise((relu(self), cond), (-relu(-self), True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Algebra.Expr.eq.Ite.apply(x, lower=S.Zero)

    Eq << Eq[-1].this.find(LessEqual).reversed

    Eq << Eq[-1].this.find(Max).apply(Tensor.Max.eq.Relu)

    Eq << Eq[-1].this.find(Min).apply(Tensor.Min.eq.Neg.Relu)





if __name__ == '__main__':
    run()
# created on 2021-12-25
