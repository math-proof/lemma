from util import *


@apply
def apply(self):
    from Lemma.Algebra.Abs.Neg import rewrite
    return Equal(self, rewrite(cosh, self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Real

    x, y = Symbol(complex=True)
    Eq << apply(cosh(x - y))

    Eq << Eq[0].this.lhs.apply(Real.Cosh.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Real.Cosh.eq.Add)




if __name__ == '__main__':
    run()
# created on 2023-11-26
