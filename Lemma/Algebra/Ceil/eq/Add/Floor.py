from util import *


@apply
def apply(self):
    n, d = self.of(Ceil[Expr / Expr])
    return Equal(self, (n - sign(d)) // d + 1)


@prove
def prove(Eq):
    from Lemma import Algebra

    n, d = Symbol(integer=True)
    Eq << apply(ceil(n / d))

    Eq << Eq[0].this.lhs.apply(Algebra.Ceil.eq.FloorDivSub_Sign)

    Eq << Eq[-1].this.lhs.apply(Algebra.Floor.eq.Add.quotient)





if __name__ == '__main__':
    run()
# created on 2019-03-07
# updated on 2023-05-29
