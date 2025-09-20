from util import *


@apply
def apply(le):
    lhs, rhs = le.of(BlockMatrix < Expr)

    args = []
    for e in lhs:
        assert len(rhs.shape) <= len(e.shape)
        args.append(e < rhs)

    return And(*args)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n, m = Symbol(integer=True, positive=True)
    a = Symbol(shape=(n,), real=True)
    b = Symbol(shape=(m,), real=True)
    x = Symbol(real=True)
    Eq << apply(BlockMatrix(a, b) < x)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.And.Lt.of.LtBlock)

    Eq << Eq[-1].this.rhs.apply(Algebra.LtBlock.given.And.Lt)




if __name__ == '__main__':
    run()
# created on 2022-04-01
