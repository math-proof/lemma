from util import *


@apply
def apply(eq_Ah, eq_Al, V):
    # upper part
    (((Q, (S[0], h)), (K, (S[h], n))), sqrt_dz), Ah = eq_Ah.of(Equal[Exp[Mul[Sliced @ Transpose[Sliced]]]])
    Vu = V[:h]
    d_z = sqrt_dz.of(Expr ** (-S.One / 2))

    # lower part
    (((S[Q], (S[h], S[n])), (S[K], (S[0], S[h]))), S[1 / sqrt(d_z)]), Al = eq_Al.of(Equal[Exp[Mul[Sliced @ Transpose[Sliced]]]])
    Vl = V[h:n]

    return Equal(softmax(Q @ K.T / sqrt(d_z) + (-1 + BlockMatrix([[Zeros(h, h), Ones(h, n - h)],
                                            [Ones(n - h, h), Zeros(n - h, n - h)]])) * oo) @ V, BlockMatrix((Ah @ Vl) / ReducedSum(Ah), Al @ Vu / ReducedSum(Al)))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Bool, Nat

    n, d_z = Symbol(integer=True, positive=True)
    h = Symbol(domain=Range(1, n))
    Q, K, V = Symbol(shape=(n, d_z), real=True)
    Ah = Symbol(shape=(h, n - h), real=True)
    Al = Symbol(shape=(n - h, h), real=True)
    Eq << apply(
        Equal(Ah, exp(Q[:h] @ K[h:n].T / sqrt(d_z))),
        Equal(Al, exp(Q[h:n] @ K[:h].T / sqrt(d_z))), V)

    i = Symbol(domain=Range(n))
    j = Symbol(integer=True)
    a = Symbol(Eq[-1].find(Mul[MatMul]))
    Eq.a_def = a.this.definition

    z = Symbol(Eq[-1].lhs)
    Ξ = Symbol(Eq[-1].find(Mul[Infinity, ~Add]) + 1)
    Eq.ksi_def = Ξ.this.definition

    Eq << Tensor.Eq.of.Eq_Block.mask.cross_attention.apply(Eq.ksi_def, a)

    a_quote = Symbol(Eq[-1].lhs.arg)
    Eq.a_quote_def = a_quote.this.definition

    Eq << Eq[-1].subs(Eq.a_quote_def.reversed)

    Eq << Eq[-1][i]

    Eq.z_def = z.this.definition

    Eq << Eq.z_def.subs(Eq.ksi_def.reversed).subs(Eq.a_def.reversed).subs(Eq.a_quote_def.reversed)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.find(softmax).apply(Tensor.Softmax.eq.Div_SumExp)

    Eq.zi_definition = Eq[-1].this.rhs.subs(Eq[-4])

    Eq << Eq.zi_definition.find(ReducedSum).this.apply(Tensor.ReducedSum.eq.Dot)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this.rhs.subs(Eq.ksi_def)

    Eq.divisor_definition = Eq[-1].this.rhs.apply(Algebra.Sum.eq.Ite)

    Eq << Eq.divisor_definition.find(ExprCondPair[2]).find(Sum).this.apply(Algebra.Sum.eq.ReducedSum)

    Eq << Eq.divisor_definition.find(ExprCondPair).find(Sum).this.apply(Algebra.Sum.eq.ReducedSum)

    Eq.divisor_definition = Eq.divisor_definition.this.rhs.subs(Eq[-2], Eq[-1], simplify=False)

    Eq << Eq.a_def[i]

    Eq <<= Eq[-1][h:n], Eq[-1][:h]

    Eq <<= Bool.EqUFnS.of.Eq.apply(Eq[-2], exp), Bool.EqUFnS.of.Eq.apply(Eq[-1], exp)

    Eq.lower_part, Eq.upper_part = Bool.Eq.of.Eq.Eq.apply(Eq[-2], Eq[0][i]), \
        Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq[1][i - h])

    Eq << Eq.divisor_definition.this.rhs.subs(Eq.lower_part, Eq.upper_part)

    Eq.zi_definition = Eq.zi_definition.subs(Eq[-1])

    Eq << Eq.zi_definition.find(MatMul).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Sum[~Mul]).args[1].definition

    Eq << Eq[-1].this.find(Sum).apply(Tensor.Sum.eq.Dot)

    Eq << Eq[-1].this.find(Sum).apply(Tensor.Sum.eq.Dot)

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.eq.Ite)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Dot.eq.Dot)

    Eq << Eq[-1].this.rhs.find(MatMul).T

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Dot.eq.Dot)

    Eq << Eq[-1].this.rhs.find(MatMul[Stack]).T

    Eq << Eq[-1].this.rhs.subs(Eq.lower_part, Eq.upper_part)

    Eq << Eq.zi_definition.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Nat.Mul_Ite.eq.Ite_MulS)

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (i,))

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.Ite.eq.Block)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Mul)

    Eq << Eq[-1].this.find(Stack[Mul[Ones]]).apply(Tensor.Stack.eq.Mul)

    Eq << Eq[-1].this.find(Stack[Pow]).apply(Tensor.Stack.eq.Pow)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.ReducedSum)

    Eq << Eq[-1].this.find(Stack[Pow]).apply(Tensor.Stack.eq.Pow)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.ReducedSum)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.z_def, Eq[-1])

    # block-diagonal mask
    # https://arxiv.org/abs/2107.02027
    # https://facebookresearch.github.io/xformers/components/ops.html?highlight=blockdiagonalmask#xformers.ops.fmha.attn_bias.BlockDiagonalMask

if __name__ == '__main__':
    run()
# created on 2022-02-20
# updated on 2022-04-01
