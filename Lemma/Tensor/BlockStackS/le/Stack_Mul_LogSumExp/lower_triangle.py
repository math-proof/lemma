from util import *


@apply
def apply(A, l):
    n, S[n] = A.shape
    assert A.is_real
    assert n >= 2 and l >= 2 and l <= n
    i = Symbol(integer=True)
    return BlockMatrix(
            Stack[i:l](BlockMatrix(-oo * Ones(l - i - 1), A[i, :i + 1])),
            Stack[i:n - l](A[i + l, i + 1:i + l + 1])) <= Stack[i:n](Ones(l) * Log(ReducedSum(Exp(A[i, relu(i + 1 - l):i + 1]))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Logic

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    Eq << apply(A, l)

    Eq << Algebra.Le.given.All.Le.apply(Eq[0])

    Eq << Algebra.Le.given.Le_0.apply(Eq[-1])

    Eq << Logic.BFn_Ite.given.OrAndS.apply(Eq[-1])

    Eq << Eq[-1].this.find(LessEqual).apply(Algebra.Le_0.given.Le)

    Eq << Eq[-1].this.find(LessEqual[Zeros]).apply(Algebra.Le_0.given.Le)

    Eq << Eq[-1].this.find(LessEqual[BlockMatrix]).apply(Algebra.LeBlock.given.And.Le)
    Eq.ou = Eq[-1].this.find(LessEqual[Mul, Log[ReducedSum[Exp]]]).apply(Algebra.Le.given.All.Le)

    Eq <<= Tensor.Le_LogSumExp.apply(Eq.ou.find(Sliced)), Tensor.Le_LogSumExp.apply(Eq.ou.args[1].find(Sliced))

    Eq <<= Eq.ou.find(Less).this.apply(Tensor.Relu.eq.Zero.of.Lt), Eq.ou.find(GreaterEqual).this.apply(Tensor.EqRelu.of.Ge)

    Eq <<= Logic.Imp_And.of.Cond.Imp.apply(Eq[-2], Eq[-4]), Logic.Imp_And.of.Cond.Imp.apply(Eq[-1], Eq[-3])

    Eq <<= Eq[-2].this.rhs.apply(Logic.Cond.of.Eq.Cond.subst, reverse=True, index=1), Eq[-1].this.rhs.apply(Logic.Cond.of.Eq.Cond.subst, reverse=True, index=1)

    Eq << Logic.Or.of.Imp.Imp.apply(Eq[-2], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-03-31
# updated on 2023-05-25
