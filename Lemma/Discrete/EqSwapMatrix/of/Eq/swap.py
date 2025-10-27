from util import *


@apply
def apply(eq):
    (w, i, j), (S[i], S[j]) = eq.of(Equal[Indexed, SwapMatrix])
    return Equal(w[i, j], w[j, i])


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor, Nat, Int

    n = Symbol(domain=Range(2, oo))
    i, j = Symbol(domain=Range(n))
    w = Symbol(real=True, shape=(n, n, n, n))
    Eq << apply(Equal(w[i, j], SwapMatrix(n, i, j)))

    t = Symbol(domain=Range(n))
    Eq << Eq[0].subs(i, t).subs(j, i).subs(t, j)

    Eq << Eq[0] @ Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(ExprCondPair[3])().find(KroneckerDelta * KroneckerDelta).simplify()

    Eq << Eq[-1].this.find(ExprCondPair[3])().find(KroneckerDelta * KroneckerDelta).simplify()

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.args[0].apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs().find(Element).simplify()

    Eq << Eq[-1].this.rhs.expr.apply(Int.Ite.eq.AddMulS)

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.eq.Eye)

    Eq << Discrete.MatPow.eq.Eye.of.Eq.apply(Eq[0])

    Eq << Eq[-1].subs(Eq[-2].reversed)

    Eq << w[i, j].inverse() @ Eq[-1]







if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-25
# updated on 2023-05-21
