from util import *


@apply
def apply(eq):
    (((((A, i), (S[0], S[i + 1])), (S[i], S[0], l)), (S[A[i + l - 1, i:i + l]], (S[i], S[0], (n, S[l])))), (S[A[i, relu(i - l + 1):i + 1]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Stack[BlockMatrix[
                Zeros,
                Exp[Sliced[Indexed]]],
                Tuple[Expr - 1]],
            Stack[Exp, Tuple[Expr + 1 - Expr]]] / Stack[Ones * ReducedSum[Exp]]])

    assert n >= 2 and l >= 2 and l <= n

    return Equal(softmax(A + (BandPart[l - 1, 0](Ones(n, n)) - 1) * oo), BlockMatrix(
        Stack[i:l - 1](BlockMatrix(z[i, l - 1 - i:], Zeros(n - 1 - i))),
        Stack[i:n - l + 1](BlockMatrix(Zeros(i), z[i + l - 1], Zeros(n - i - l)))))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Set, Logic

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, l), real=True)
    Eq << apply(Equal(z, BlockMatrix(
            Stack[i:l - 1](BlockMatrix(Zeros(l - i - 1), Exp(A[i, :i + 1]))),
            Stack[i:n - l + 1](Exp(A[i + l - 1, i:i + l]))) / Stack[i:n](Ones(l) * ReducedSum(Exp(A[i, relu(i + 1 - l):i + 1])))))

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

    Eq << Eq[-1].this.rhs.apply(Tensor.Softmax.eq.Mul.ReducedSum)

    Eq.zi_def = Eq[-1].this.rhs.subs(Eq.a_quote_exp[i])

    Eq << Eq.ksi_def[i].this.find(BandPart).defun()

    Eq.ksi_def = Eq[-1].this.rhs.expr.apply(Logic.Bool.eq.Ite)

    Eq << Eq.zi_def.find(ReducedSum).this.subs(Eq.ksi_def)

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedSum.eq.Sum)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InAdd, i)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.ReducedSum)

    Eq << Eq[-1].this.find(Max).apply(Tensor.Max.eq.Relu)

    Eq << Eq[-1].this(i).find(Min).simplify()

    Eq << Eq.zi_def.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Indexed).defun()

    Eq << Eq[-1].this.find(BandPart).defun()

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    j = Eq.ksi_def.rhs.variable
    Eq << Eq[-1][j]

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Ite)

    Eq.zij_def = Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InNeg)

    z_dquote = Symbol('z^\"', Eq[1].rhs)
    Eq.z_dquote_def = z_dquote.this.definition

    Eq.zi_dquote_def = Eq.z_dquote_def[i]

    Eq << Eq.zi_dquote_def[j]

    Eq << Eq[-1].this.find(ExprCondPair[2]).expr.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, i=0)

    Eq << Eq[-1].this.find(And).apply(Set.Cond.Cond.Is.In.Ico)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InSub, i)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InNeg)

    Eq << Eq[-1].this.rhs.apply(Logic.Ite_Ite.eq.Ite__Ite)

    Eq.zij_dquote_def = Eq[-1].this.rhs.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq.zi_quote_def = Eq[0][i]

    Eq << Eq.zi_quote_def[j + Min(l, n) - i - 1]

    Eq << Eq.zij_dquote_def.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this(j).find(Symbol < 0).simplify()

    Eq << Eq[-1].this.find(And).apply(Algebra.And.collect, cond=Eq[-1].find(Element))

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InNeg)

    Eq << Eq[-1].this.find(Symbol < Symbol + 1).apply(Algebra.Lt.Is.Le.strengthen)

    Eq << Eq[-1].this.find(Symbol < Symbol + 1).apply(Algebra.Lt.Is.Le.strengthen)

    Eq << Eq[-1].this(i, j).find(And).apply(Set.OrLe.Or.Is.In_Ico.BandPart.lower.offset)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InNeg)

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq.zij_def, Eq[-1])

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq.z_dquote_def, Eq[-1])

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq.z_def, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-12-29
# updated on 2022-03-29
