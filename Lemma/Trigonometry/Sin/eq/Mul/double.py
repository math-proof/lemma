from util import *


@apply
def apply(self):
    x = self.of(Sin)
    return Equal(self, 2 * sin(x / 2) * cos(x / 2))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(sin(x * 2))

    y = Symbol(real=True)
    Eq << sin(x + y).this.apply(Trigonometry.Sin.eq.Add)

    Eq << Eq[-1].subs(y, x)


if __name__ == '__main__':
    run()
# created on 2023-10-03
