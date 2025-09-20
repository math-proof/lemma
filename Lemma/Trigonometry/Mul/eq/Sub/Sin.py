from util import *


@apply
def apply(self):
    y, x = self.of(Sin * Cos)
    return Equal(self, (sin(x + y) - sin(x - y)) / 2)


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x, y = Symbol(real=True)
    Eq << apply(sin(y) * cos(x))

    Eq << Eq[-1].this.find(Sin[Expr - Expr]).apply(Trigonometry.Sin.eq.Add)

    Eq << Eq[-1].this.find(Sin[Expr + Expr]).apply(Trigonometry.Sin.eq.Add)


if __name__ == '__main__':
    run()
# created on 2023-06-01
