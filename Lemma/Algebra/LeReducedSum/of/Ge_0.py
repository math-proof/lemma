from util import *


@apply
def apply(ge):
    x = ge.of(Expr >= Zeros)
    n, = x.shape
    assert x.is_real
    return x <= ReducedSum(x) * Ones(*x.shape)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(real=True, shape=(n,), given=True)
    Eq << apply(x >= Zeros(n))

    Eq << Algebra.Le.given.All.Le.apply(Eq[1])

    Eq << Eq[-1].this.find(ReducedSum).apply(Algebra.ReducedSum.eq.Sum)

    i = Eq[-1].lhs.index
    Eq << Eq[-1].find(Sum).this.apply(Algebra.Sum.eq.AddSumS, cond={i})

    Eq << Algebra.All.Ge.of.Ge.apply(Eq[0], i)

    Eq << Algebra.Ge_0.Sum.of.Ge_0.apply(Eq[-1], (i, Range(n) - {i}))

    Eq << Algebra.GeAdd.of.Eq.Ge.apply(Eq[-3], Eq[-1])

    Eq << Bool.AllIn.of.All.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this(i).find(Element).simplify()

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2022-04-01
# updated on 2023-03-25
