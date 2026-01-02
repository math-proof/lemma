from util import *


@apply
def apply(eq_relu, eq_min, A, V):
    ((i, l), limit_i), β = eq_relu.of(Equal[Stack[relu[Expr + 1 - Expr]]])
    ((n, (S[i], u)), S[limit_i]), ζ = eq_min.of(Equal[Stack[Min[Add]]])
    S[i], S[0], S[n] = limit_i
    S[n], S[n] = A.shape

    indices = slice(β[i], ζ[i])
    return Equal(softmax(A + (BandPart[l - 1, u - 1](Ones(n, n)) - 1) * oo) @ V, Stack[i:n](softmax(A[i, indices]) @ (V[indices])))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Set, Discrete, Bool, Vector

    n, l, u, d_z = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    A = Symbol(real=True, shape=(n, n))
    V = Symbol(real=True, shape=(n, d_z))
    β, ζ = Symbol(integer=True, shape=(n,))
    (Eq.beta, Eq.zeta), Eq.objective = apply(Equal(β, Stack[i:n](relu(i - l + 1))), Equal(ζ, Stack[i:n](Min(i + u, n))), A, V)

    band_part = Eq.objective.find(BandPart)
    Eq << Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool.apply(exp(A) * band_part).reversed

    a_quote = Symbol(Eq[-1].lhs.arg)
    Eq.a_quote_def = a_quote.this.definition

    Eq << Eq[-1].subs(Eq.a_quote_def.reversed)

    Xi = Symbol(band_part)
    Eq.Xi_definition = Xi.this.definition

    Eq << Eq[-1].subs(Eq.Xi_definition.reversed)

    Eq << Eq[-1][i]

    z = Symbol(Eq.objective.lhs)
    Eq.z_definition = z.this.definition

    Eq << Eq.z_definition.subs(Eq.a_quote_def.reversed)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.find(softmax).apply(Tensor.Softmax.eq.DivExp_KeepdimSumExp)

    Eq.zi_definition = Eq[-1].this.rhs.subs(Eq[-4])

    Eq << Eq.Xi_definition.this.rhs.defun()

    Eq << Eq[-1][i]

    Eq.Xi_definition = Eq[-1].this.rhs.expr.apply(Bool.Bool.eq.Ite)

    Eq << Eq.zi_definition.find(ReducedSum).this.arg.args[0].subs(Eq.Xi_definition)

    Eq << Eq[-1].this.rhs.apply(Vector.Sum.eq.Sum_Get)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Icc.Is.InAdd, i)

    Eq.start_definition = Eq.beta[i].this.rhs.defun()

    Eq << Eq[-1].subs(Eq.start_definition.reversed, Eq.zeta[i].reversed)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.ReducedSum)

    Eq.zi_definition = Eq.zi_definition.subs(Eq[-1])

    Eq << Eq.zi_definition.rhs.args[0].this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.domain_defined)

    k = Eq[-1].rhs.expr.variable
    Eq << Eq.Xi_definition[k]

    Eq << Eq[-2].this.rhs.expr.expr.subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.start_definition.reversed, Eq.zeta[i].reversed)

    Eq << Eq[-1].this.rhs.expr.apply(Tensor.Sum.eq.Dot)

    Eq << Eq[-1].this.rhs.expr.T

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack_Dot.eq.DotSliceS)

    Eq << Eq.zi_definition.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.find(exp).apply(Tensor.Exp.eq.MulSoftmax_KeepdimSumExp)

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (i, 0, n))

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.z_definition, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2020-12-28
# updated on 2022-03-30


