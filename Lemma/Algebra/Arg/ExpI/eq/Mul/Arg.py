from util import *


@apply
def apply(self):
    z, r = self.of(Arg[Exp[ImaginaryUnit * Arg * Expr]])
    assert r <= 1 and r >= -1 or 1 / r >= 1 or 1 / r <= -1
    return Equal(self, Arg(z) * r)


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    z = Symbol(complex=True)
    Eq << apply(Arg(exp(S.ImaginaryUnit * Arg(z) / n)))

    Eq << Eq[0].this.lhs.apply(Algebra.Arg.ExpI.eq.Add.Ceil)

    Eq << Eq[-1].this.find(Ceil).apply(Algebra.CeilSubDivArg.eq.Zero)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)




if __name__ == '__main__':
    run()
# created on 2018-11-06
# updated on 2022-04-03
