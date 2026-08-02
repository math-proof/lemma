from util import *


@apply
def apply(given, index=-1):
    lhs, rhs = given.of(Equal)
    from Lemma.Algebra.Expr.eq.Block import split
    if index < 0:
        index += lhs.shape[0]

    assert index < lhs.shape[0] and index > 0
    lhs = split(lhs, index)
    rhs = split(rhs, index)

    lhs0, lhs1 = lhs.of(BlockMatrix)
    rhs0, rhs1 = rhs.of(BlockMatrix)

    return Equal(lhs0, rhs0), Equal(lhs1, rhs1)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n + 1,))
    y = Symbol(real=True, shape=(oo,))
    Eq << apply(Equal(x, y[:n + 1]))

    Eq << Eq[0][:n]

    Eq << Eq[0][n]




if __name__ == '__main__':
    run()


# created on 2019-05-01
# updated on 2023-03-26
