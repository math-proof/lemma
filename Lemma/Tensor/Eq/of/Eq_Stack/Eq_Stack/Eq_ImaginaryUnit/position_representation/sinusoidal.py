from util import *


@apply
def apply(eq_PE, eq_PE_quote, eq_Z):
    ((((i, (b, (j, d))), (S[j], S[0])), (S[i / b ** ((j - 1) / d)], S[S.true])), j_limit, i_limit), PE = eq_PE.of(Equal[Stack[Piecewise[ExprCondPair[sin[Expr * Expr ** (-Expr / Expr)], Equal[Expr % 2]], ExprCondPair[cos]]]])
    (((S[i * (b ** (-j / d))], (S[j], S[0])), (S[i / b ** ((j - 1) / d)], S[S.true])), S[j_limit], S[i_limit]), PE_quote = eq_PE_quote.of(Equal[Stack[Piecewise[ExprCondPair[cos, Equal[Expr % 2]], ExprCondPair[-sin]]]])
    S[j], S[0], S[d] = j_limit
    S[i], S[0], n = i_limit

    (S[PE], S[PE_quote]), Z = eq_Z.of(Equal[ImaginaryUnit * Expr - Expr])

    return Equal(Z[i, j], exp(S.ImaginaryUnit * (S.Pi / 2 * (2 - j % 2) - i / b ** (2 * (j // 2) / d))))


@prove
def prove(Eq):
    from Lemma import Algebra, Trigonometry, Tensor, Bool

    n, b = Symbol(positive=True, integer=True)
    d = Symbol(integer=True, positive=True, even=True)
    PE, PE_quote, Z = Symbol(real=True, shape=(n, d))
    i, j = Symbol(integer=True)
    Eq << apply(
        Equal(PE, Stack[j:d, i:n](Piecewise((sin(i / b ** (j / d)), Equal(j % 2, 0)), (cos(i / b ** ((j - 1) / d)), True)))),
        Equal(PE_quote, Stack[j:d, i:n](Piecewise((cos(i / b ** (j / d)), Equal(j % 2, 0)), (-sin(i / b ** ((j - 1) / d)), True)))),
        Equal(Z, S.ImaginaryUnit * PE - PE_quote))

    F = Symbol(Stack[j:d, i:n](cos(i / b ** (2 * (j // 2) / d))))
    F_quote = Symbol(Stack[j:d, i:n](sin(i / b ** (2 * (j // 2) / d))))
    Eq.f_def = F.this.definition

    Eq.f_quote_def = F_quote.this.definition

    Eq <<= Eq.f_def.this.find(Floor).apply(Algebra.Floor.eq.Ite), Eq.f_quote_def.this.find(Floor).apply(Algebra.Floor.eq.Ite)

    Eq <<= Eq[-2].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite, simplify=None), Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite, simplify=None)

    Eq <<= Eq[-2].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS, simplify=None), Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS, simplify=None)

    Eq <<= Eq[-2].this.find(Pow[Piecewise]).apply(Algebra.Pow_Ite.eq.Ite_PowS, simplify=None), Eq[-1].this.find(Pow[Piecewise]).apply(Algebra.Pow_Ite.eq.Ite_PowS, simplify=None)

    Eq <<= Eq[-2].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite, simplify=None), Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite, simplify=None)

    Eq <<= Eq[-2].this.find(Cos[Piecewise]).apply(Trigonometry.Cos.eq.Ite), Eq[-1].this.find(Sin[Piecewise]).apply(Trigonometry.Sin.eq.Ite)

    Eq <<= Eq[-2].this.find(Add).apply(Algebra.AddMulS.eq.Mul_Add, simplify=None), Eq[-1].this.find(Add).apply(Algebra.AddMulS.eq.Mul_Add, simplify=None)

    Eq.F_def = Eq[-2].this.find(Mul[Add]).apply(Algebra.Mul.Neg, simplify=None)

    Eq.F_quote_def = Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.Neg, simplify=None)

    k = Symbol(integer=True)
    Eq.PE_definition = Eq[0][i + k, j]

    Eq.PE_quote_definition = Eq[1][i + k, j]

    Eq << Eq.PE_definition.find(sin).this.arg.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq.PE_definition.find(cos).this.arg.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq <<= Eq[-2].this.rhs.apply(Trigonometry.Sin.eq.Add), Eq[-1].this.rhs.apply(Trigonometry.Cos.eq.Sub)

    Eq.cossin = Eq.PE_definition.this.rhs.subs(Eq[-2], Eq[-1])

    Eq << Eq[0][i, j] * Eq.F_def[k, j]

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Ite.eq.Ite_MulS, simplify=None)

    Eq << Eq[1][i, j] * Eq.F_quote_def[k, j]

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Ite.eq.Ite_MulS, simplify=None)

    Eq << Eq[-1] + Eq[-3]

    Eq << Eq[-1].this.rhs.apply(Algebra.AddIteS.eq.IteAnd, simplify=None)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.cossin, Eq[-1])

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (j, 0, d))

    Eq.PE_equality = Eq[-1].this.rhs.apply(Tensor.Stack.eq.Add)

    Eq << Eq.PE_quote_definition.find(cos).this.arg.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq.PE_quote_definition.find(sin).this.arg.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq <<= Eq[-2].this.rhs.apply(Trigonometry.Cos.eq.Sub), Eq[-1].this.rhs.apply(Trigonometry.Sin.eq.Add)

    Eq <<= Bool.Eq.of.Eq.Eq.apply(Eq[-4], Eq[-2])

    Eq << Eq.PE_quote_definition.this.rhs.subs(Eq[-3])

    Eq.coscos = Eq[-1].this.rhs.subs(Eq[-3])

    Eq << Eq[0][i, j] * Eq.F_quote_def[k, j]

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Ite.eq.Ite_MulS, simplify=None)

    Eq << Eq[1][i, j] * Eq.F_def[k, j]

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Ite.eq.Ite_MulS, simplify=None)

    Eq << Eq[-1] - Eq[-3]

    Eq << Eq[-1].this.rhs.apply(Algebra.AddIteS.eq.IteAnd)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.coscos, Eq[-1])

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (j, 0, d))

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.eq.Add)

    I = S.ImaginaryUnit
    Eq << I * Eq.PE_equality - Eq[-1]

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.collect(PE[i])

    Eq.collect = Eq[-1].this.rhs.collect(PE_quote[i])

    z = Symbol(F - S.ImaginaryUnit * F_quote)
    Eq << z[k].this.definition

    Eq << Eq[-1] * I

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq.collect.subs(Eq[-1].reversed, Eq[-3].reversed)

    Eq << Eq[-1].this.rhs.collect(z[k])

    Eq << Eq[2][i]

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[2][k + i]

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].subs(k, 1)

    Eq.geometric_progression = Algebra.Eq.of.Eq.geometric_progression.apply(Eq[-1], n=i)

    Eq << z[1].this.definition

    Eq <<= Eq.f_def[1], Eq.f_quote_def[1]

    Eq << Eq[-3].this.rhs.subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Tensor.Add_Stack.eq.Stack_Add)

    Eq << Eq[-1].this.find(Add).apply(Trigonometry.Add.eq.ExpI.Euler)

    Eq << Eq.geometric_progression.subs(Eq[-1])

    Eq.geometric_progression = Eq[-1][j]

    Eq << Eq[2][0, j]

    Eq <<= Eq[0][0, j], Eq[1][0, j]

    Eq << Eq[-3].this.rhs.subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite, simplify=None)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Algebra.AddIteS.eq.IteAnd, simplify=None)

    Eq << Eq.geometric_progression.subs(Eq[-1])

    Eq << Eq[3].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.apply(Algebra.ExpAdd.eq.MulExpS)

    Eq.eq_euler = Eq[-1].this.find(exp).apply(Trigonometry.ExpMulI.eq.AddCos_MulISin.Euler)

    Eq << Algebra.Mod.eq.Ite.apply(Eq.eq_euler.find(Mod))

    Eq << Eq[-1] / -2

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Ite, simplify=None)

    Eq << Eq[-1] + 1

    Eq << Eq[-1].this.rhs.apply(Algebra.Add_Ite.eq.Ite_AddS, simplify=None)

    Eq << Eq[-1] * S.Pi

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Ite, simplify=None)

    Eq <<= Trigonometry.EqCos.of.Eq.apply(Eq[-1]), Trigonometry.EqSin.of.Eq.apply(Eq[-1])

    Eq << Eq.eq_euler.subs(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite, simplify=None)

    Eq << Eq[-1].this.find(Add).apply(Algebra.AddIteS.eq.IteAnd, simplify=None)





if __name__ == '__main__':
    run()
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
# created on 2020-12-31
# updated on 2022-01-23
