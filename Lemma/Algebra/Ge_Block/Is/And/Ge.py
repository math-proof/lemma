from util import *


@apply
def apply(le):
    lhs, rhs = le.of(Expr >= BlockMatrix)

    args = []
    for e in rhs:
        assert len(lhs.shape) <= len(e.shape)
        args.append(lhs >= e)

    return And(*args)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n, m = Symbol(integer=True, positive=True)
    a = Symbol(shape=(n,), real=True)
    b = Symbol(shape=(m,), real=True)
    x = Symbol(real=True)
    Eq << apply(x >= BlockMatrix(a, b))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.And.Ge.of.Ge_Block)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge_Block.given.And.Ge)




if __name__ == '__main__':
    run()
# created on 2022-04-01
