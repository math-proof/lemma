from util import *


@apply
def apply(self):
    x, y = self.of(Sin[Expr - Expr])
    return Equal(sin(x - y), sin(x) * cos(y) - cos(x) * sin(y))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x, y = Symbol(real=True)
    Eq << apply(sin(x - y))



    Eq << Eq[0].this.lhs.apply(Trigonometry.Sin.eq.Add)


if __name__ == '__main__':
    run()
# created on 2020-11-24
# updated on 2023-06-01

