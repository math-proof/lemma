from util import *


@apply(simplify=False)
def apply(self, factor=None):
    return Equal(self, self.rewrite(self, factor=factor, collect=True), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, b, x, y = Symbol(complex=True)
    Eq << apply(a * x - a * y + b + b * y, factor=b)

    Eq << Eq[0].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)




if __name__ == '__main__':
    run()
# created on 2018-08-02
# updated on 2023-05-20
