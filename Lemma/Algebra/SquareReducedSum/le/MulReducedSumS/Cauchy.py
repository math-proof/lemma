from util import *


@apply
def apply(a, b):
    n, = a.shape
    S[n], = a.shape
    return ReducedSum(a * b) ** 2 <= ReducedSum(a ** 2) * ReducedSum(b ** 2)


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(domain=Range(2, oo))
    a, b = Symbol(shape=(n,), real=True, given=True)
    Eq << apply(a, b)

    x = Symbol(real=True)
    Eq << ReducedSum((x * a + b) ** 2).this.arg.apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedSum.eq.Add)

    Eq << GreaterEqual(Eq[-1].lhs, 0, plausible=True)

    Eq << Algebra.GeAdd.of.Eq.Ge.apply(Eq[-2].reversed, Eq[-1])

    Eq << ~Eq[-1]

    Eq << Algebra.Any_Lt_0.given.Add.gt.Zero.apply(Eq[-1])

    Eq << Eq[-1] / 4

    Eq << Eq[-1].this.apply(Algebra.Gt.transport, lhs=0)

    Eq << ~Eq[-1]





if __name__ == '__main__':
    run()
# created on 2022-04-02
# updated on 2022-04-03
