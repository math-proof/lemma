from util import *


@apply
def apply(self):
    from Lemma.Finset.AddSumS.eq.Sum_Add_Sum import piece_together
    return Equal(self, piece_together(Cap, self))


@prove
def prove(Eq):
    from Lemma import Set
    k, i = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    f, g = Function(etype=dtype.integer)
    Eq << apply(Cap[i:n, k:n, n:m](f(k)) & Cap[k:n, n:m](g(k)))

    Eq << Eq[0].this.rhs.apply(Set.Cap.eq.Inter)


if __name__ == '__main__':
    run()

# created on 2021-04-28
from . import limits
