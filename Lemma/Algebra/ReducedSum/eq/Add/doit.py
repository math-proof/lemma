from util import *


@apply
def apply(self):
    from Lemma.Algebra.ReducedSum.eq.Sum import rewrite
    from Lemma.Algebra.Sum.eq.Add.doit import doit
    return Equal(self, doit(Sum, rewrite(self)))


@prove
def prove(Eq):
    from Lemma import Algebra

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    n = 5
    Eq << apply(ReducedSum(x[:n]))

    Eq << Eq[-1].this.lhs.apply(Algebra.ReducedSum.eq.Sum)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.doit)




if __name__ == '__main__':
    run()
# created on 2023-08-20
