from util import *


@apply
def apply(self):
    arg = self.of(Norm)
    return Equal(self, Norm(~arg))


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    Eq << apply(Norm(x))

    Eq << Eq[0].this.lhs.apply(Algebra.Norm.eq.Sqrt)

    Eq << Eq[-1].this.rhs.apply(Algebra.Norm.eq.Sqrt)


if __name__ == '__main__':
    run()
# created on 2023-06-24
