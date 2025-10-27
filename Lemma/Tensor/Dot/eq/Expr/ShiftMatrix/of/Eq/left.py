from util import *


@apply
def apply(eq, x):
    (i, j), wij = eq.of(Equal[ShiftMatrix])
    n, = x.shape
    return Equal(wij.T @ wij @ x, x)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor, Nat

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), real=True)
    w = Symbol(shape=(n, n, n, n), real=True)
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(w[i, j], ShiftMatrix(n, i, j)), x)

    Eq << Eq[0].T

    i, j = Eq[0].lhs.indices
    w = Eq[0].lhs.base
    Eq << (w[i, j] @ x).this.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs().expr.args[2]().expr.simplify(wrt=Eq[-1].rhs.variable)

    Eq << Eq[-1].this.rhs().expr.args[2].expr.args[2]().expr.simplify()

    Eq << (w[i, j].T @ Eq[-1]).this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.expr.args[2].expr.apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs().expr.args[1]().expr.simplify(wrt=Eq[-1].rhs.variable)

    Eq << Eq[-1].this.find(Stack)().find(Element).simplify()

    Eq << Eq[-1].this.rhs().expr.args[1]().expr.simplify()




if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-13
# updated on 2023-05-21
