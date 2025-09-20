from util import *


@apply
def apply(self):
    n, d = self.of(Ceil[Expr / Expr] - 1)
    return Equal(self, (n - sign(d)) // d)


@prove
def prove(Eq):
    from Lemma import Algebra

    n, d = Symbol(integer=True)
    Eq << apply(Ceil(n / d) - 1)

    Eq << Eq[0].this.find(Ceil).apply(Algebra.Ceil.eq.FloorDivSub_Sign)

    Eq << Eq[-1].this.lhs.find(Floor).apply(Algebra.Floor.eq.Add.quotient)





if __name__ == '__main__':
    run()
# created on 2018-08-11
# updated on 2023-05-29
