from util import *


@apply
def apply(le):
    lhs, rhs = le.of(Expr < BlockMatrix)

    args = []
    for e in rhs:
        assert len(lhs.shape) <= len(e.shape)
        args.append(lhs < e)

    return tuple(args)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n, m = Symbol(integer=True, positive=True)
    a = Symbol(shape=(n,), real=True)
    b = Symbol(shape=(m,), real=True)
    x = Symbol(real=True)
    Eq << apply(x < BlockMatrix(a, b))

    Eq << Algebra.Lt.given.All.Lt.apply(Eq[0])

    Eq << Logic.BFn_Ite.given.OrAndS.apply(Eq[-1])

    Eq << Algebra.All.Lt.of.Lt.apply(Eq[1])

    i = Eq[-1].rhs.index
    Eq << Logic.AllIn.of.All.apply(Eq[-1], (i, Range(-oo, n)), simplify=None)

    Eq.infer_lt = Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Algebra.All.Lt.of.Lt.apply(Eq[2])

    Eq << Eq[-1].subs(i, i - n)

    Eq << Logic.AllIn.of.All.apply(Eq[-1], (i, Range(n, oo)), simplify=None)

    Eq << Logic.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Logic.Or.of.Imp.Imp.apply(Eq.infer_lt, Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-04-01
# updated on 2023-04-29
