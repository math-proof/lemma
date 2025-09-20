from util import *


@apply
def apply(self):
    x = self.of(Re)
    return Equal(self, (x + ~x) / 2)


@prove
def prove(Eq):
    from Lemma import Algebra

    z = Symbol(complex=True)
    Eq << apply(Re(z))

    Eq << Eq[0].this.rhs.apply(Algebra.Add.eq.Mul.Re)

    Eq << Eq[-1].this.rhs.find(Re).apply(Algebra.Re.eq.Mul)


if __name__ == '__main__':
    run()
# created on 2023-06-24
