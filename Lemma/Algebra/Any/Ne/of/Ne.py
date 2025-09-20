from util import *


@apply
def apply(self, i=None):
    from Lemma.Algebra.Ne.Is.Any.Ne import rewrite
    return rewrite(self, i)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=True)
    f, g = Symbol(shape=(oo,), real=True, given=True)
    Eq << apply(Unequal(Stack[k:n](f[k]), Stack[k:n](g[k])))

    Eq << ~Eq[1]

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.lhs.apply(Tensor.Expr.eq.Stack, k)

    Eq << Eq[-1].this.rhs.apply(Tensor.Expr.eq.Stack, k, simplify=None)

    Eq << ~Eq[-1]



if __name__ == '__main__':
    run()
# created on 2023-05-01
