from util import *


@apply
def apply(eq_C):
    (C, S[C]), C_quote = eq_C.of(Equal[Mul[Transpose[Ones * ReducedSum[Expr ** 2] ** (1 / 2)] ** -1]])
    return abs(C_quote @ C_quote.T) <= 1


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor, Nat, Rat

    n, d = Symbol(domain=Range(2, oo))
    C, C_quote = Symbol(shape=(n, d), real=True)
    Eq << apply(Equal(C_quote, C / (sqrt(ReducedSum(C * C) * Ones(d, n))).T))

    Eq << Algebra.LeAbs.given.And.apply(Eq[1])

    Eq <<= Algebra.Le.given.All.Le.apply(Eq[-2]), Algebra.Ge.given.All.Ge.apply(Eq[-1])

    i = Eq[-1].find(Indexed).index
    Eq <<= Algebra.Le.given.All.Le.apply(Eq[-2]), Algebra.Ge.given.All.Ge.apply(Eq[-1])

    j = Eq[-1].find(Indexed[2]).index
    Eq <<= Eq[-2].subs(Eq[0]), Eq[-1].subs(Eq[0])

    Eq <<= Eq[-2].this.find(MatMul).apply(Tensor.Dot.eq.ReducedSum), Eq[-1].this.find(MatMul).apply(Tensor.Dot.eq.ReducedSum)

    Eq << Eq[0][i]

    Eq << Rat.Ne_0.of.Div1.gt.Zero.apply(Eq[-1])

    Eq << Nat.Gt_0.of.Ne_0.apply(Eq[-1])

    Eq << Eq[-1].subs(i, j)

    Eq <<= Algebra.Le_1.of.Gt_0.Gt_0.apply(Eq[-1], Eq[-2]), Algebra.Gt_0.Sqrt.of.Gt_0.apply(Eq[-1]) * Algebra.Gt_0.Sqrt.of.Gt_0.apply(Eq[-2])

    Eq << Nat.LeMul.of.Gt_0.Le.apply(Eq[-1], Eq[-2])

    Eq << Algebra.And.of.LeAbs.apply(Eq[-1])

    Eq << Algebra.LeDiv.of.Gt_0.Le.apply(Eq[-4], Eq[-2])

    Eq << Algebra.GeDiv.of.Gt_0.Ge.apply(Eq[-4], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-04-02
# updated on 2023-06-25
