from util import *


@apply
def apply(self, *, evaluate=False):
    plus, d = self.of(Floor[Expr / Expr])
    n = plus - d + sign(d)
    return Equal(self, Ceil(n / d, evaluate=evaluate))


@prove
def prove(Eq):
    from Lemma import Algebra

    n, d = Symbol(integer=True)
    Eq << apply(n // d)

    Eq << Algebra.Ceil.eq.FloorDivSub_Sign.apply(Eq[0].rhs).reversed





if __name__ == '__main__':
    run()
# created on 2019-05-09
# updated on 2023-05-29
