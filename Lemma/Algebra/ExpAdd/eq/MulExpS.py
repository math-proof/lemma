from util import *


@apply
def apply(self):
    args = self.of(Exp[Add])

    args = [exp(e) for e in args]

    return Equal(self, Mul(*args), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    b, a = Symbol(real=True)
    Eq << apply(exp(a + b))

    Eq << Algebra.Eq.given.EqLogS.apply(Eq[-1])
    Eq << Eq[-1].this.rhs.apply(Real.LogMul.eq.AddLogS)


if __name__ == '__main__':
    run()
# created on 2018-08-28
