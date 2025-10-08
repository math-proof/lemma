from util import *


@apply
def apply(le):
    lhs, rhs = le.of(Expr > BlockMatrix)

    args = []
    for e in rhs:
        assert len(lhs.shape) <= len(e.shape)
        args.append(lhs > e)

    return tuple(args)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Tensor, Set

    n, m = Symbol(integer=True, positive=True)
    a = Symbol(shape=(n,), real=True)
    b = Symbol(shape=(m,), real=True)
    x = Symbol(real=True)
    Eq << apply(x > BlockMatrix(a, b))

    Eq << Algebra.All.Gt.of.Gt.apply(Eq[0])

    Eq << Bool.OrAndS.of.BFn_Ite.apply(Eq[-1])

    Eq << Bool.And.Imp.of.Or.apply(Eq[-1])

    Eq <<= Bool.All.of.Imp.single_variable.apply(Eq[-2], simplify=None), Bool.All.of.Imp.single_variable.apply(Eq[-1], simplify=None)

    Eq <<= Set.AllIn_SDiff.of.All.apply(Eq[-2], domain=Range(0, n), simplify=None), Set.AllIn_SDiff.of.All.apply(Eq[-1], domain=Range(n, m + n), simplify=None)

    Eq << Tensor.GtStack.of.All_Gt.apply(Eq[-2])

    Eq << Tensor.GtStack.of.All_Gt.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-04-01
# updated on 2023-04-29
