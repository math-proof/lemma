from util import *


@apply
def apply(self):
    x = self.of(Cos)
    return Equal(self, cos(x / 2) ** 2 - sin(x / 2) ** 2)


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(cos(x * 2))

    y = Symbol(real=True)
    Eq << cos(x + y).this.apply(Trigonometry.Cos.eq.Sub)

    Eq << Eq[-1].subs(y, x)


if __name__ == '__main__':
    run()
# created on 2023-10-03
