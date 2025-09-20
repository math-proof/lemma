from util import *


@apply
def apply(self):
    x = self.of(Abs ** 2)
    return Equal(self, x * ~x)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(complex=True)
    Eq << apply(abs(x) ** 2)

    Eq << Eq[0].this.rhs.apply(Algebra.Mul.Conj.eq.Square.Abs)


if __name__ == '__main__':
    run()
# created on 2023-06-24
