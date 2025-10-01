from util import *


@apply
def apply(eq):
    ((((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n) - 1, i:i + Min(l, n) - 1]], (S[i], S[0], S[n - Min(l, n) + 1]))), ((((S[A], S[i]), (S[i], (S[i], (S[n], u)))), (S[i], S[0], (S[1], S[n], S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u) + 1]), (S[i + n - Min(n, u) + 1], S[n])), (S[i], S[0], (S[n], S[u]))))), (S[A[i][relu(i - l + 1):Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[BlockMatrix[1][
        BlockMatrix[
            Stack[
                BlockMatrix[
                    Zeros,
                    Exp[Sliced[Indexed]]
                ],
                Tuple[Min - 1]
                ],
            Stack[Exp]
            ],
        BlockMatrix[
            Stack[Exp[Sliced[Indexed, Tuple[Add[Min]]]], Tuple[Add]],
            Stack[
                BlockMatrix[
                    Exp[Sliced[Indexed]],
                    Zeros
                    ],
                Tuple[Min - 1]
                ]
            ]
        ] / Stack[Ones * ReducedSum[Exp]]])

    assert n >= 2 and u >= 2
    breadth = Add(Min(l, n), Min(u, n), -1)
    return Equal(softmax(A + (BandPart[l - 1, u - 1](Ones(n, n)) - 1) * oo), BlockMatrix(
        Stack[i:Min(l, n) - 1](BlockMatrix(z[i, Min(l, n) - 1 - i:Min(l, n) - 1], Zeros(n - i))),
        Stack[i:n - Min(l, n) + 1](BlockMatrix(Zeros(i), z[i + Min(l, n) - 1,:Min(l, n) - 1], Zeros(n - i - Min(l, n) + 1)))) + BlockMatrix(
        Stack[i:n - Min(u, n) + 1](BlockMatrix(Zeros(i), z[i, Min(l, n) - 1:], Zeros(n - i - Min(u, n)))),
        Stack[i:Min(u, n) - 1](BlockMatrix(Zeros(n - Min(u, n) + i + 1), z[i + n - Min(u, n) + 1, Min(l, n) - 1:breadth - i - 1]))))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Set, Logic

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), real=True)
    Eq << apply(Equal(z, BlockMatrix[1](
        BlockMatrix(
            Stack[i:Min(l, n) - 1](BlockMatrix(Zeros(Min(l, n) - i - 1), Exp(A[i,:i]))),
            Stack[i:n - Min(l, n) + 1](Exp(A[i + Min(l, n) - 1, i:i + Min(l, n) - 1]))),
        BlockMatrix(
        Stack[i:n - Min(u, n) + 1](Exp(A[i, i:i + Min(u, n)])),
        Stack[i:Min(u, n) - 1](BlockMatrix(Exp(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:]), Zeros(i + 1))))) / Stack[i:n](Ones(breadth) * ReducedSum(Exp(A[i, relu(i + 1 - l):Min(n, i + u)])))))

    Ξ = Symbol(Eq[1].find(BandPart))
    Eq.ksi_def = Ξ.this.definition

    Eq << Algebra.Mul.eq.Exp.Infty.apply(exp(A) * Ξ).reversed

    a_quote = Symbol(Eq[-1].lhs.arg)
    Eq.a_quote_def = a_quote.this.definition

    Eq.a_quote_exp = Eq[-1].subs(Eq.a_quote_def.reversed)

    z = Symbol(Eq[1].lhs)
    Eq.z_def = z.this.definition

    Eq << Eq.z_def.subs(Eq.ksi_def.reversed, Eq.a_quote_def.reversed)

    i = Eq[1].find(Stack).variable
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

    Eq << Eq.zi_def.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Indexed).defun()

    Eq << Eq[-1].this.find(BandPart).defun()

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    j = Eq.ksi_def.rhs.variable
    Eq << Eq[-1][j]

    Eq.zij_def = Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Ite)

    z_dquote = Symbol('z^\"', Eq[1].rhs)
    Eq.z_dquote_def = z_dquote.this.definition

    Eq.zi_dquote_def = Eq.z_dquote_def[i]

    Eq << Eq.zi_dquote_def[j]

    Eq << Eq[-1].this.find(Piecewise[ExprCondPair[3]]).apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, i=0)

    Eq << Eq[-1].this.rhs.args[0].find(Piecewise[ExprCondPair[3]]).apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, i=0)

    Eq << Eq[-1].this.find(And).apply(Set.Cond.Cond.Is.In.Ico, simplify=None)

    Eq << Eq[-1].this.find(And).apply(Set.Cond.Cond.Is.In.Ico, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InSub, i, simplify=None)

    Eq << Eq[-1].this.find(Element[Symbol]).apply(Set.In_Icc.Is.InSub, i, simplify=None)

    Eq << Eq[-1].this.rhs.args[1].apply(Logic.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this.rhs.args[1].apply(Logic.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this.rhs.args[0].apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq << Eq[-1].this.rhs.args[1].apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq << Eq[-1].this.find(And).apply(Algebra.And.collect, cond=Eq[-1].find(Element))

    Eq << Eq[-1].this(i, j).find(And).apply(Set.Or.Or.Is.In.Ico.BandPart.lower.offset)

    Eq << Eq[-1].this.find(And).apply(Algebra.And.collect, cond=Eq[-1].rhs.args[1].find(Element))

    Eq.zij_dquote_def = Eq[-1].this(i, j).find(And).apply(Set.Or.Or.Is.In.Ico.BandPart.upper.offset)

    Eq.zi_quote_def = Eq[0][i]

    Eq << Eq.zi_quote_def[j + Min(l, n) - i - 1]

    Eq << Eq.zij_dquote_def.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this(j).find(Symbol < Symbol).simplify()

    Eq << Eq[-1].this(j).find(Symbol < 0).simplify()

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq.zij_def, Eq[-1])

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq.z_dquote_def, Eq[-1])

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq.z_def, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-01
# updated on 2023-05-21
