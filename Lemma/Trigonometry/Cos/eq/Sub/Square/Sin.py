from util import *


@apply
def apply(self):
    x = self.of(Cos)
    return Equal(self, 1 - 2 * sin(x / 2) ** 2)


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(cos(x * 2))

    Eq << Eq[0].this.lhs.apply(Trigonometry.Cos.eq.Sub.double)

    Eq << Eq[-1].this.find(cos ** 2).apply(Trigonometry.Square.Cos.eq.Sub.Square.Sin)


if __name__ == '__main__':
    run()
# created on 2023-10-03
