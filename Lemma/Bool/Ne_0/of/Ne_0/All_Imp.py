from util import *


@apply
def apply(f0, suffice, n=None):
    assert n.is_given == False

    f0.of(Unequal[0])
    fn, fn1 = suffice.of(Imply)
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, 0) == f0
    assert n.domain.min() == 0

    return fn


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Set, Bool, Tensor

    n = Symbol(integer=True, nonnegative=True, given=False)
    f = Symbol(integer=True, shape=(oo,))
    Eq << apply(Unequal(f[0], 0), Imply(Unequal(f[n], 0), Unequal(f[n + 1], 0)), n=n)

    D = Symbol(Stack[n](KroneckerDelta(f[n], 0)))
    Eq.D0_is_zero = Equal(D[0], 0, plausible=True)

    Eq << Eq.D0_is_zero.this.lhs.definition

    Eq.or_statement = Or(Equal(D[n + 1], 0), Equal(D[n], 1), plausible=True)

    Eq << Eq.or_statement.this.args[1].lhs.definition

    Eq << Eq[-1].this.args[0].lhs.definition

    Eq << Eq[-1].this.args[0].reversed

    Eq << Eq[1].apply(Bool.Or.of.ImpNot)

    Eq.is_multiplication_zero = Algebra.Mul.eq.Zero.of.OrEqS.apply(Eq.or_statement)

    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    E = Symbol(Identity(m) + Stack[j:m, i:m](KroneckerDelta(i + 1, j) * -D[j]))
    Eq << E.this.definition

    Eq << (D[:m] @ E).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.expr.expr.args[1].definition

    Eq << Eq[-1].this.rhs.expr.expr.expand()

    Eq << Eq[-1].this.rhs.apply(Tensor.Add_Stack.eq.Stack_Add)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.expr.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Eq[-1].this.rhs().find(NotElement).simplify()

    Eq << Eq[-1].this.rhs.expr.apply(Bool.Ite.subst)

    Eq << Eq[-1].subs(Eq.D0_is_zero)

    Eq << Eq.is_multiplication_zero.this.lhs.expand()

    Eq << Eq[-1].subs(n, i - 1)

    Eq << Eq[-1].this.args[1].apply(Set.NotInAdd.of.NotIn, 1)

    Eq << Bool.All.of.All_OrNot.apply(Eq[-1], 1)

    Eq << Bool.UFn.of.UFn.Eq.apply(Eq[-1].reversed, Eq[-5])

    k = Symbol(integer=True)
    E_quote = Symbol("E'", Stack[j:m, i:m](Piecewise((Product[k:i + 1:j + 1](D[k]), j >= i), (0, True))))
    Eq.D_is_zero = Eq[-1] @ E_quote

    Eq << (E @ E_quote).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.rhs.expr.expr.args[0].definition

    Eq << Eq[-1].this.rhs().expr.simplify()

    Eq << Eq[-1].this.rhs.expr.expr.args[0].definition

    Eq << Eq[-1].this.rhs.expr.expr.expand()

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InSub, 1)

    Eq << (-Eq[-1].rhs.expr.args[0].args[0].expr).this.apply(Algebra.Mul_Prod.eq.Prod)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs().expr.apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs().expr.simplify(wrt=True)

    Eq << Bool.Ite__Ite.eq.IteAnd_Not__Ite.apply(Eq[-1].rhs.expr)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs().expr.simplify()

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Ite.eq.AddMulS)

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.eq.Eye)

    Eq << Eq.D_is_zero.subs(Eq[-1])

    Eq << Eq[-1][m - 1]

    Eq << Eq[-1].subs(m, n + 1)

    Eq << Eq[-1].this.lhs.definition





if __name__ == '__main__':
    run()

# created on 2018-04-16
# updated on 2023-05-23
