from util import *


@apply
def apply(self):
    args = self.of(Abs[Mul])
    return Equal(self, Mul(*(abs(arg) for arg in args)))


@prove
def prove(Eq):
    from Lemma import Algebra, Int
    x, y = Symbol(real=True)
    Eq << apply(abs(x * y))

    Eq << Eq[0].this.rhs.apply(Int.MulAbsS.eq.AbsMul)


if __name__ == '__main__':
    run()
# created on 2018-02-12
