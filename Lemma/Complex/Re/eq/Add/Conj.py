from util import *


@apply
def apply(self):
    x = self.of(Re)
    return Equal(self, (x + ~x) / 2)


@prove
def prove(Eq):
    from Lemma import Complex

    z = Symbol(complex=True)
    Eq << apply(Re(z))

    Eq << Eq[0].this.rhs.apply(Complex.Add.eq.Mul.Re)

    Eq << Eq[-1].this.rhs.find(Re).apply(Complex.Re.eq.Mul)


if __name__ == '__main__':
    run()
# created on 2023-06-24
