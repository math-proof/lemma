from util import *


@apply
def apply(self):
    expr = self.of(ReducedSum)
    n = expr.shape[0]
    return Equal(self, ReducedSum(expr[:n - 1]) + expr[n - 1], evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Vector

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(oo,), real=True)
    Eq << apply(ReducedSum(x[:n + 1]))

    Eq << Eq[0].this.lhs.apply(Vector.Sum.eq.Sum_Get)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.ReducedSum)



if __name__ == '__main__':
    run()
# created on 2023-04-19
