from util import *


@apply
def apply(eq_A, eq_P, eq_P_quote, eq_I_quote, eq_I_dquote):
    ((I, k), limit), A = eq_A.of(Equal[Stack[Bool[Indexed > 0]]])
    assert I >= 0
    S[k], S[0], n = limit
    ((S[k], S[limit]), (A, (S[k], S[limit]))), P = eq_P.of(Equal[Stack + ReducedArgMax[Symbol * Stack] + (2 - n)])
    (S[P], (S[P[k]], S[limit])), P_quote = eq_P_quote.of(Equal[Symbol * Stack[Bool[Expr >= 0]]])
    (S[0], S[I]), I_quote = eq_I_quote.of(Equal[BlockMatrix])
    (S[I_quote[P_quote[k]]], S[limit]), I_dquote = eq_I_dquote.of(Equal[Stack])

    return Equal(ReducedSum(I_dquote), ReducedSum(I))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Logic

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True) # seq_length
    A = Symbol(integer=True, shape=(n,)) # attention_mask = (input_ids > 0).int()
    P = Symbol(integer=True, shape=(n,))
    # position_ids = torch.arange(1, seq_length + 1)[None, ].to(attention_mask.device)
    # position_ids += attention_mask.argmax(-1, keepdim=True)
    P_quote = Symbol(integer=True, shape=(n,))
    # position_ids *= (position_ids >= 0).int()
    I = Symbol(integer=True, nonnegative=True, shape=(n,)) # input_ids
    I_quote = Symbol(integer=True, shape=(n + 1,)) # input_ids = hstack(input_ids, 1)
    I_dquote = Symbol('I^"', integer=True, shape=(n,)) # input_ids = torch.gather(input_ids, 1, position_ids)
    Eq << apply(
        Equal(A, Stack[k:n](Bool(I[k] > 0))),
        Equal(P, Stack[k:n](k) + ReducedArgMax(A * Stack[k:n](k)) + 2 - n),
        Equal(P_quote, P * Stack[k:n](Bool(P[k] >= 0))),
        Equal(I_quote, BlockMatrix(0, I)),
        Equal(I_dquote, Stack[k:n](I_quote[P_quote[k]])))

    Eq << Eq[-1].this.lhs.apply(Algebra.ReducedSum.eq.Sum, k)

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedSum.eq.Sum, k)

    Eq << Eq[-1].subs(Eq[4], simplify=None)

    Eq << Eq[-1].subs(Eq[3], simplify=None)

    Eq << Eq[-1].subs(Eq[2], simplify=None)

    Eq << Eq[-1].subs(Eq[1], simplify=None)

    Eq << Eq[-1].this.find(Piecewise).apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, simplify=None)

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.GeMul.Is.And, simplify=None)

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite, simplify=None)

    Eq << Eq[-1].this.find(Piecewise).apply(Logic.Ite_Ite.eq.Ite__Ite)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.subst.offset, -Eq[-1].find(ReducedArgMax) - 1 + n)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add.split, cond=k <= Eq[-1].find(ReducedArgMax))

    Eq << Tensor.Eq_0.Sum.of.Eq_Stack.padding_right.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-11-05
