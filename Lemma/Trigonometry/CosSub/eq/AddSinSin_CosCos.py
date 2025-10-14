from util import *


@apply
def apply(self):
    x, y = self.of(Cos[Expr - Expr])
    return Equal(self, cos(x) * cos(y) + sin(x) * sin(y))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x, y = Symbol(real=True)
    Eq << apply(cos(x - y))

    Eq << Eq[-1].this.lhs.apply(Trigonometry.Cos.eq.Sub)

    # https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F




if __name__ == '__main__':
    run()
# created on 2020-11-19
# updated on 2023-06-01


