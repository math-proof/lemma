from util import *


@apply
def apply(eq_cup, subset, Q, K, V, K_quote, V_quote):
    cup, m = eq_cup.of(Equal[Card])
    (d, j), j_limit = cup.of(Cup[FiniteSet[Indexed]])
    S[j], S[0], S[m] = j_limit
    n, d_z = Q.shape
    S[cup], (S[0], S[n]) = subset.of(Subset[Expr, Range])
    return Equal(softmax(Q @ (K + K_quote).T / sqrt(d_z) + (Stack[j:n](Bool(Element(j, cup))) - Ones(n, n)) * oo) @ (V + V_quote), \
                 softmax(Q @ (Stack[j:m](K[d[j]]).T + Transpose[0, 2](Stack[j:m](K_quote[:, d[j]]))) / sqrt(d_z)) @ (Stack[j:m](V[d[j]]) + Transpose[0, 1](Stack[j:m](V_quote[:, d[j]]))))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Set, Discrete, Bool, Vector

    n, k, m = Symbol(integer=True, positive=True)
    r = Symbol(shape=(n,), integer=True)
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    V = Symbol(shape=(n, d_z), real=True)
    d = Symbol(shape=(oo,), integer=True)
    i, j = Symbol(integer=True)
    K_quote = Symbol(shape=(n, n, d_z), real=True)
    V_quote = Symbol(shape=(n, n, d_z), real=True)
    s = d[:m].cup_finiteset(j)
    Eq << apply(
        Equal(Card(s), m),
        Subset(s, Range(n)),
        Q, K, V, K_quote, V_quote)

    a = Symbol(Eq[-1].find(Mul[MatMul]))
    Eq.a_def = a.this.definition

    z = Symbol(Eq[2].lhs)
    Eq.z_def = z.this.definition

    Eq << Eq.z_def[i]

    Xi = Symbol(Eq[-1].find(Stack))
    Eq.Xi_def = Xi.this.definition

    Eq << Eq[-1].this.rhs.subs(Eq.Xi_def.reversed, Eq.a_def[i].reversed)

    Eq << Eq[-1].this.find(softmax).apply(Tensor.Softmax.eq.DivExp_KeepdimSumExp)

    Eq << Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool.apply(exp(a[i]) * Xi).reversed

    Eq.zi_definition = Eq[-2].subs(Eq[-1])

    Eq << Eq.zi_definition.find(ReducedSum).this.subs(Eq.Xi_def)

    Eq << Eq[-1].this.rhs.apply(Vector.Sum.eq.Sum_Get, j)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.absorb)

    Eq.eq_intersect = Set.EqInter.of.Subset.apply(Eq[1])

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq << Set.EqReducedSum.of.Eq_Card.apply(Eq[0], Eq[-1].find(Sum))

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])

    Eq.zi_definition = Eq.zi_definition.subs(Eq[-1])

    Eq << Eq.zi_definition.find(MatMul).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.domain_defined)

    k = Eq[-1].rhs.expr.variable
    Eq << Eq.Xi_def[k]

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.absorb)

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq << Set.EqSum.of.Eq_Card.apply(Eq[0], Eq[-1].find(Sum))

    Eq << Eq[-1].this.rhs.apply(Tensor.Sum.eq.Dot)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.expr.T

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack_Dot.eq.DotSliceS)

    Eq << Eq.zi_definition.subs(Eq[-1])

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Exp.eq.Mul.Softmax)

    Eq << Eq[-1].subs(Eq.a_def)

    Eq << Eq[-1].this.find(Stack[Mul]).apply(Tensor.Stack.eq.Mul)

    Eq << Eq[-1].this.find(Stack[MatMul]).apply(Tensor.Stack_Dot.eq.DotSliceS)

    Eq << Eq[-1].this.find(Stack[Tuple[2]]).apply(Tensor.Stack.eq.Transpose)

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack_Dot.eq.DotSliceS)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Softmax.eq.Softmax)

    Eq << Eq[-1].this.find(Stack[MatMul]).apply(Tensor.Stack_Dot.eq.DotSliceS)

    Eq << Eq[-1].this.find(Transpose[Stack]).apply(Tensor.Transpose.eq.Stack)

    Eq << Eq[-1].this.find(Stack[Add]).apply(Tensor.Stack.eq.Add)

    Eq << Eq[-1].this.find(Add[~Stack[Tuple[2]]]).apply(Tensor.Stack.eq.Transpose, axis=(0, 1))

    Eq << Eq[-1].this.find(Stack[Add]).apply(Tensor.Stack.eq.Add)

    Eq << Eq[-1].this.find(Stack[Tuple[2]]).apply(Tensor.Stack.eq.Transpose)

    Eq << Eq[-1].this.find(Stack[Tuple[3]]).apply(Tensor.Stack.eq.Transpose)

    Eq << Eq[-1].this.find(Stack[Tuple[2]]).apply(Tensor.Stack.eq.Transpose, axis=(0, 1))

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.z_def, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2022-01-11
# updated on 2023-03-19
