from util import *


@apply
def apply(self):
    b, e = self.of(Pow)
    assert e % 2 == 0
    return Equal(self, (-b) ** e, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    n = Symbol(integer=True, even=True)
    Eq << apply((x - y) ** n)
    Eq << Eq[-1].this.lhs.apply(Algebra.Pow.eq.Mul.Neg)


if __name__ == '__main__':
    run()
# created on 2021-11-25
