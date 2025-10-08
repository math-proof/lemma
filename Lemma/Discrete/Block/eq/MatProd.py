from util import *


@apply
def apply(n, m, b):
    i = Symbol(integer=True)

    return Equal(BlockMatrix(BlockMatrix(MatProduct[i:m](SwapMatrix(n, i, b[i])), Zeros(n)).T,
                             BlockMatrix(Zeros(n), 1)).T,
                             MatProduct[i:m](SwapMatrix(n + 1, i, b[i])))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Bool, Tensor

    n = Symbol(domain=Range(2, oo))
    m = Symbol(positive=True, integer=True, given=False)
    b = Symbol(integer=True, shape=(oo,), nonnegative=True)
    Eq << apply(n, m, b)

    Eq.initial = Eq[0].subs(m, 1)

    Eq.concatenate = Discrete.Block.eq.SwapMatrix.apply(n)

    * _, i, j = Eq.concatenate.rhs.args
    Eq << Eq.concatenate.subs(i, 0).subs(j, b[0]).T

    Eq.induct = Eq[0].subs(m, m + 1)

    Eq << Eq.induct.this.rhs.apply(Tensor.MatProd.eq.Dot.pop)

    Eq << Eq[-1].subs(Eq[0].reversed)

    Eq << Eq.concatenate.subs(i, m).subs(j, b[m]).T

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Block, deep=True)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.MatProd.push)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n=m, start=1)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-31
# updated on 2023-09-17
