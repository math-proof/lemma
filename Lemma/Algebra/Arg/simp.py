from util import *


@apply
def apply(self):
    z = self.of(Arg[Exp[Arg * S.ImaginaryUnit]])
    return Equal(self, Arg(z))


@prove
def prove(Eq):
    from Lemma import Algebra

    z = Symbol(complex=True)
    Eq << apply(Arg(exp(S.ImaginaryUnit * Arg(z))))

    Eq << Eq[0].this.lhs.apply(Algebra.Arg.ExpI.eq.Add.Ceil)

    Eq << Eq[-1].this.find(Ceil).apply(Algebra.CeilSubDivArg.eq.Zero)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2019-03-01
