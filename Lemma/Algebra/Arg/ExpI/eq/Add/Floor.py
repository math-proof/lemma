from util import *


@apply
def apply(self):
    x = self.of(Arg[Exp[ImaginaryUnit * Expr]])
    return Equal(self, x + Floor(-x / (S.Pi * 2) + S.One / 2) * S.Pi * 2)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    Eq << apply(Arg(exp(S.ImaginaryUnit * x)))

    Eq << Eq[-1].this.lhs.apply(Algebra.Arg.ExpI.eq.Add.Ceil) / 2

    Eq << Eq[-1].this.rhs.apply(Algebra.Floor.eq.Neg.Ceil)


if __name__ == '__main__':
    run()
# created on 2019-03-01
