from util import *


@apply
def apply(eq):
    (((((A, i), (S[0], S[i + 1])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n), i + 1:i + Min(l, n) + 1]], (S[i], S[0], S[n - Min(l, n)]))), (S[A[i, relu(i - l + 1):i + 1]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Stack[BlockMatrix[
                Zeros,
                Exp[Sliced[Indexed]]],
                Tuple[Min]],
            Stack[Exp]] / Stack[Ones * ReducedSum[Exp]]])

    assert n >= 2 and l >= 2

    breadth = Min(l, n)
    return Equal(softmax(A + (BandPart[l - 1, 0](Ones(n, n)) - 1) * oo), BlockMatrix(
        Stack[i:breadth](BlockMatrix(z[i, breadth - i - 1:], Zeros(n - 1 - i))),
        Stack[i:n - breadth](BlockMatrix(Zeros(i + 1), z[i + breadth], Zeros(n - 1 - i - breadth)))))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Set, Bool, Nat, Vector

    n, l = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, Min(l, n)), real=True)
    Eq << apply(Equal(z, BlockMatrix(
            Stack[i:Min(l, n)](BlockMatrix(Zeros(Min(l, n) - i - 1), Exp(A[i, :i + 1]))),
            Stack[i:n - Min(l, n)](Exp(A[i + Min(l, n), i + 1:i + Min(l, n) + 1]))) / Stack[i:n](Ones(Min(l, n)) * ReducedSum(Exp(A[i, relu(i + 1 - l):i + 1])))))

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

    Eq << Eq[-1].this.rhs.apply(Vector.Sum.eq.Sum_Get)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InAdd, i)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.ReducedSum)

    Eq << Eq[-1].this.find(Max).apply(Tensor.Max.eq.Relu)

    Eq << Eq[-1].this(i).find(Min).simplify()

    Eq << Eq.zi_def.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Indexed).defun()

    Eq << Eq[-1].this.find(BandPart).defun()

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    j = Eq.ksi_def.rhs.variable
    Eq << Eq[-1][j]

    Eq << Eq[-1].this.find(Mul).apply(Nat.Mul_Ite.eq.Ite_MulS)

    Eq.zij_def = Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InNeg)

    z_dquote = Symbol('z^\"', Eq[1].rhs)
    Eq.z_dquote_def = z_dquote.this.definition

    Eq.zi_dquote_def = Eq.z_dquote_def[i]

    Eq << Eq.zi_dquote_def[j]

    Eq << Eq[-1].this.find(ExprCondPair[2]).expr.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, i=0)

    Eq << Eq[-1].this.find(And).apply(Set.Cond.Cond.Is.In.Ico)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InSub, i)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InNeg)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite_Ite.eq.Ite__Ite)

    Eq.zij_dquote_def = Eq[-1].this.rhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq.zi_quote_def = Eq[0][i]

    Eq << Eq.zi_quote_def[j + Min(l, n) - i - 1]

    Eq << Eq.zij_dquote_def.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this(j).find(Symbol < 0).simplify()

    Eq << Eq[-1].this.find(And).apply(Algebra.And.collect, cond=Eq[-1].find(Element))

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InNeg)

    Eq << Eq[-1].this.find(Symbol < Symbol + 1).apply(Algebra.Lt.Is.Le.strengthen)

    Eq << Eq[-1].this.find(Symbol < Symbol + 1).apply(Algebra.Lt.Is.Le.strengthen)

    Eq << Eq[-1].this(i, j).find(And).apply(Set.OrGe.Or.Is.In.Ico.BandPart.lower)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InNeg)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.zij_def, Eq[-1])

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.z_dquote_def, Eq[-1])

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.z_def, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-02

# updated on 2022-04-01
