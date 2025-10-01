from util import *


@apply
def apply(all_is_positive, eq_initial):
    ((L, i, S[i]), R), (S[i], S[0], t) = all_is_positive.of(All[Element[Indexed]])
    assert R in Interval.open(0, oo)

    (A, S[t], S[t]), ((((ξ, S[i]), S[L[i, :i + 1]]), (S[ξ[i]], S[(BlockMatrix(ξ[i + 1:t], 1) @ L[i + 1:t + 1, :i + 1] @ L[i, :i + 1])])), (S[i],)) = \
    eq_initial.of(Indexed + Sum[Indexed ** 2 * Norm ** 2 + 2 * Expr * Expr] > 0)

    return A[t, t] > Norm(L[t, :t]) ** 2

@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Set, Logic, Tensor

    n = Symbol(domain=Range(10, oo))
    A = Symbol(shape=(n, n), real=True)
    L = Symbol(shape=(n, n), super_real=True)
    i = Symbol(integer=True)
    t = Symbol(domain=Range(3, n))
    ξ = Symbol(r'{\color{red} {ξ}}', real=True, shape=(oo,))
    Eq << apply(
           All[i:t](Element(L[i, i], Interval.open(0, oo))),
           A[t, t] + Sum[i](ξ[i] ** 2 * Norm(L[i, :i + 1]) ** 2 + 2 * ξ[i] * (BlockMatrix(ξ[i + 1:t], 1) @ L[i + 1:t + 1, :i + 1] @ L[i, :i + 1])) > 0)

    k = Symbol(domain=Range(0, t), given=False)
    Eq.hypothesis = Greater(A[t, t] + Sum[i:k:t](Eq[1].find(Sum).expr) - Norm(BlockMatrix(ξ[k:t], 1) @ L[k:t + 1, :k]) ** 2, 0, plausible=True)

    Eq.induct = Eq.hypothesis.subs(k, k + 1)

    Eq << Eq.hypothesis.find(Norm **  2).this.apply(Tensor.Sum.Square.Abs.eq.Add.Norm.Dot.recursive.real)

    Eq << Eq.hypothesis.find(Sum).this.apply(Algebra.Sum.eq.Add.shift)

    Eq.gt_zero = Eq.hypothesis.subs(*Eq[-2:])

    Eq <<= Eq.gt_zero.find(Indexed ** 2 * Norm ** 2).this.args[1].apply(Algebra.Square.Norm.eq.Add.pop).this.rhs.apply(Algebra.Mul_Add.eq.AddMulS),\
        Eq.gt_zero.find(-2 * Expr).this.find(Expr @ Expr @ Expr).apply(Tensor.Dot.eq.Sub.push)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Dot.eq.Dot)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq.Lkk_is_positive = Algebra.Cond.of.All.subst.apply(Eq[0], i, k)

    Eq.eq_square_Lkk = Set.Eq.Square.Abs.of.IsReal.apply(Eq.Lkk_is_positive)

    Eq << Eq.gt_zero.subs(Eq[-4], Eq[-1], Eq.eq_square_Lkk)

    # now start the square completing process:
    Eq << Set.IsPositive.Square.of.IsPositive.apply(Eq.Lkk_is_positive)

    Eq << Set.Eq.of.IsNotZero.square_completing.apply(Eq[-1], Add(*[arg for arg in Eq[-2].lhs.args if arg._has(ξ[k])]), ξ[k], simplify=None)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].subs(ξ[k], -Eq[-1].find(Indexed ** 2 * Add ** 2).find(Mul))

    Eq << Eq[-1].this.find(Norm[BlockMatrix @ Sliced] ** 2).apply(Algebra.Square.Norm.eq.Sub.push)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Dot.eq.Dot)

    Eq << Eq[-1].this.find(Abs ** 2).apply(Algebra.Square.Abs.eq.Mul.Conj)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.All_Imp.apply(Eq[1], Eq[-1], k, 0)

    Eq << Eq.induct.subs(k, t - 1)

    Eq << Algebra.Gt.of.Sub.gt.Zero.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-06-29
# updated on 2023-06-30
