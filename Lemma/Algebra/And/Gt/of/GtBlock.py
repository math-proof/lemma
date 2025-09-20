from util import *


@apply
def apply(le):
    lhs, rhs = le.of(BlockMatrix > Expr)

    args = []
    for e in lhs:
        assert len(rhs.shape) <= len(e.shape)
        args.append(e > rhs)

    return tuple(args)


@prove
def prove(Eq):
    from Lemma import Algebra

    n, m = Symbol(integer=True, positive=True)
    a = Symbol(shape=(n,), real=True)
    b = Symbol(shape=(m,), real=True)
    x = Symbol(real=True)
    Eq << apply(BlockMatrix(a, b) > x)

    Eq << Algebra.And.Lt.of.Lt_Block.apply(Eq[0].reversed)

    Eq << Eq[-2].reversed
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2022-04-01
