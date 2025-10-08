from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], (n, u)))), (S[i], S[0], (S[1], S[n],  S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u) + 1]), (S[i + n - Min(n, u) + 1], S[n])), (S[i], S[0], (n, u)))), (S[A[i][i:Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Stack[Exp[Sliced[Indexed, Tuple[Add[Min]]]], Tuple[Add]],
            Stack[
                BlockMatrix[
                    Exp[Sliced[Indexed]],
                    Zeros],
                Tuple[Min - 1]]] / Stack[Ones * ReducedSum[Exp]]])

    assert n >= 2 and u >= 2

    breadth = Min(u, n) - 1
    return Equal(softmax(A + (BandPart[0, u - 1](Ones(n, n)) - 1) * oo), BlockMatrix(
        Stack[i:n - breadth](BlockMatrix(Zeros(i), z[i], Zeros(n - 1 - i - breadth))),
        Stack[i:breadth](BlockMatrix(Zeros(n - breadth + i), z[i + n - breadth, :breadth - i]))))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Set, Bool

    n, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, Min(u, n)), real=True)
    Eq << apply(Equal(z, BlockMatrix(
        Stack[i:n - Min(u, n) + 1](Exp(A[i, i:i + Min(u, n)])),
        Stack[i:Min(u, n) - 1](BlockMatrix(Exp(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:]), Zeros(i + 1)))) / Stack[i:n](Ones(Min(u, n)) * ReducedSum(Exp(A[i, i:Min(n, i + u)])))))

    i = Eq[1].find(Stack).variable
    Ξ = Symbol(Eq[1].find(BandPart))
    Eq.ksi_def = Ξ.this.definition

    Eq << Algebra.Mul.eq.Exp.Infty.apply(exp(A) * Ξ).reversed

    a_quote = Symbol(Eq[-1].lhs.arg)
    Eq.a_quote_def = a_quote.this.definition

    Eq.a_quote_exp = Eq[-1].subs(Eq.a_quote_def.reversed)

    z = Symbol(Eq[1].lhs)
    Eq.z_def = z.this.definition

    Eq << Eq.z_def.subs(Eq.ksi_def.reversed, Eq.a_quote_def.reversed)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(Tensor.Softmax.eq.Div_SumExp)

    Eq.zi_def = Eq[-1].this.rhs.subs(Eq.a_quote_exp[i])

    Eq << Eq.ksi_def[i].this.find(BandPart).defun()

    Eq.ksi_def = Eq[-1].this.rhs.expr.apply(Bool.Bool.eq.Ite)

    Eq << Eq.zi_def.find(ReducedSum).this.subs(Eq.ksi_def)

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedSum.eq.Sum)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InAdd, i)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.ReducedSum)

    Eq << Eq[-1].this(i).find(Max).simplify()

    Eq << Eq.zi_def.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Indexed).defun()

    Eq << Eq[-1].this.find(BandPart).defun()

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    j = Eq.ksi_def.rhs.variable
    Eq << Eq[-1][j]

    Eq.zij_def = Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Ite)

    z_dquote = Symbol('z^\"', Eq[1].rhs)
    Eq.z_dquote_def = z_dquote.this.definition

    Eq.zi_dquote_def = Eq.z_dquote_def[i]

    Eq << Eq.zi_dquote_def[j]

    Eq << Eq[-1].this.find(ExprCondPair).expr.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, i=0)

    Eq << Eq[-1].this.find(And).apply(Set.Cond.Cond.Is.In.Ico, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InSub, i, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite_Ite.eq.Ite__Ite)

    Eq.zij_dquote_def = Eq[-1].this.rhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq.zi_quote_def = Eq[0][i]

    Eq << Eq.zi_quote_def[j - i]

    Eq << Eq.zij_dquote_def.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this(j).find(Symbol < Symbol).simplify()

    Eq << Eq[-1].this.find(And).apply(Algebra.And.collect, cond=Eq[-1].find(Element))

    Eq << Eq[-1].this(i, j).find(And).apply(Set.Or.Or.Is.In.Ico.BandPart.upper.offset)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.zij_def, Eq[-1])

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.z_dquote_def, Eq[-1])

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.z_def, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-01
# updated on 2022-01-23
