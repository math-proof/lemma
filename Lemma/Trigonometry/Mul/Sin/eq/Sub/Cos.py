from util import *


@apply
def apply(self):
    x, y = self.of(Sin * Sin)
    return Equal(self, (cos(x - y) - cos(x + y)) / 2)


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x, y = Symbol(real=True)
    Eq << apply(sin(x) * sin(y))

    Eq << Eq[-1].this.find(Cos[Expr - Expr]).apply(Trigonometry.Cos.eq.Add)

    Eq << Eq[-1].this.find(Cos[Expr + Expr]).apply(Trigonometry.Cos.eq.Sub)




if __name__ == '__main__':
    run()
# created on 2023-06-01
