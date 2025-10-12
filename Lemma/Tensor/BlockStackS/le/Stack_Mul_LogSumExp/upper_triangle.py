from util import *


@apply
def apply(A, u):
    n, S[n] = A.shape
    assert A.is_real
    assert n >= 2 and u >= 2 and u <= n
    i = Symbol(integer=True)
    return BlockMatrix(
            Stack[i:n - u](A[i, i:i + u]),
            Stack[i:u](BlockMatrix(A[i + n - u, n - u + i:], -oo * Ones(i)))) <= Stack[i:n](Ones(u) * Log(ReducedSum(Exp(A[i, i:Min(n, i + u)]))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Bool, Nat

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    Eq << apply(A, u)

    Eq << Algebra.Le.given.All.Le.apply(Eq[0])

    Eq << Algebra.Le.given.Le_0.apply(Eq[-1])

    Eq << Bool.BFn_Ite.given.OrAndS.apply(Eq[-1])

    Eq << Eq[-1].this.find(LessEqual).apply(Algebra.Le_0.given.Le)

    Eq << Eq[-1].this.find(LessEqual[Zeros]).apply(Algebra.Le_0.given.Le)

    Eq << Eq[-1].this.find(LessEqual[BlockMatrix]).apply(Algebra.LeBlock.given.And.Le)

    Eq.ou = Eq[-1].this.find(LessEqual[Mul, Log[ReducedSum[Exp]]]).apply(Algebra.Le.given.All.Le)

    Eq <<= Tensor.Le_LogSumExp.apply(Eq.ou.args[1].find(Sliced)), Tensor.Le_LogSumExp.apply(Eq.ou.find(Sliced))

    Eq <<= Eq.ou.find(Less).this.apply(Algebra.Lt.of.Lt.transport, rhs=1), Eq.ou.find(GreaterEqual).this.apply(Algebra.Ge.of.Ge.transport, rhs=1)

    Eq <<= Eq[-1].this.rhs.apply(Algebra.EqMin.of.Ge), Eq[-2].this.rhs.apply(Nat.EqMin.of.Lt)

    Eq <<= Bool.Imp_And.of.Cond.Imp.apply(Eq[-2], Eq[-6]), Bool.Imp_And.of.Cond.Imp.apply(Eq[-1], Eq[-5])

    Eq <<= Eq[-2].this.rhs.apply(Bool.Cond.of.Eq.Cond.subst, reverse=True, index=1), Eq[-1].this.rhs.apply(Bool.Cond.of.Eq.Cond.subst, reverse=True, index=1)

    Eq << Bool.Or.of.Imp.Imp.apply(Eq[-2], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-04-01
# updated on 2023-05-25
