from util import *


@apply
def apply(self):
    (x, y), (S[x], S[y]) = self.of(Cos * Cos + Sin * Sin)
    return Equal(self, cos(x - y))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x, y = Symbol(real=True)
    Eq << apply(cos(x) * cos(y) + sin(x) * sin(y))

    Eq << Eq[-1].this.rhs.apply(Trigonometry.Cos.eq.Add)

    # https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F



if __name__ == '__main__':
    run()
# created on 2023-06-01

