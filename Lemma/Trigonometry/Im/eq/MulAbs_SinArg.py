from util import *


@apply
def apply(self):
    z = self.of(Im)

    return Equal(self, abs(z) * sin(Arg(z)))


@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra

    z = Symbol(complex=True, given=True)
    Eq << apply(Im(z))

    Eq << Eq[0].this.find(sin).apply(Trigonometry.Sin.Arg.eq.Ite)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Ite)

    Eq << Eq[-1].this.find(Abs).apply(Algebra.Abs.eq.Sqrt)




if __name__ == '__main__':
    run()
# created on 2018-07-25
# updated on 2022-01-23
