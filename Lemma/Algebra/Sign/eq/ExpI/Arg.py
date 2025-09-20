from util import *


@apply
def apply(self):
    x = self.of(Sign)
    assert x.is_nonzero
    return Equal(self, Exp(S.ImaginaryUnit * Arg(x)))


@prove
def prove(Eq):
    from Lemma import Algebra

    z = Symbol(complex=True, zero=False)
    Eq << apply(Sign(z))

    Eq << Eq[0].lhs.this.apply(Algebra.Sign.eq.Ite.Abs)

    Eq << Algebra.Expr.eq.MulAbs_ExpMulIArg.apply(z)

    Eq << Eq[-2].this.rhs.subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-25
