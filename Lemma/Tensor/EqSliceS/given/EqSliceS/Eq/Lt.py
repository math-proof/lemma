from util import *


@apply
def apply(given, index=-1):
    lhs, rhs = given.of(Equal)
    from Lemma.Algebra.Expr.eq.Block import split

    lhs = split(lhs, index)
    rhs = split(rhs, index)

    lhs0, lhs1 = lhs.of(BlockMatrix)
    rhs0, rhs1 = rhs.of(BlockMatrix)

    first = Equal(lhs0, rhs0)
    second = Equal(lhs1, rhs1)

    return first, second


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n + 1,))
    y = Symbol(real=True, shape=(oo,))
    Eq << apply(Equal(x, y[:n + 1]))

    Eq << Eq[-2] @ BlockMatrix([Identity(n), Zeros(n)]).T

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()

    Eq << BlockMatrix(Zeros(n), x[n]).this.subs(Eq[2])

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()





if __name__ == '__main__':
    run()

# created on 2019-03-24
# updated on 2021-12-06