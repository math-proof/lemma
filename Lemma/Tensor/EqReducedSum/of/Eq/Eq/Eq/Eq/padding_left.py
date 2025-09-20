from util import *


@apply
def apply(eq_A, eq_P, eq_P_quote, eq_I_quote):
    ((I, k), limit), A = eq_A.of(Equal[Stack[Bool[Indexed > 0]]])
    assert I >= 0
    S[k], S[0], n = limit
    ((S[k], S[limit]), (A, (S[k], S[limit]))), P = eq_P.of(Equal[Stack + ReducedArgMax[Symbol * Stack] + (1 - n)])
    (S[P], (S[P[k]], S[limit])), P_quote = eq_P_quote.of(Equal[Symbol + n * Stack[Bool[Expr < 0]]])
    (S[I[P_quote[k]]], S[limit]), I_quote = eq_I_quote.of(Equal[Stack])

    return Equal(ReducedSum(I_quote), ReducedSum(I))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True) # seq_length
    A = Symbol(integer=True, shape=(n,)) # attention_mask = (input_ids > 0).int()
    P = Symbol(integer=True, shape=(n,))
    # position_ids = torch.arange(1, seq_length + 1)[None, ].to(attention_mask.device)
    # position_ids = position_ids + (1 - seq_length) + (position_ids * attention_mask).argmax(-1, keepdim=True)
    P_quote = Symbol(integer=True, shape=(n,))# position_ids += (position_ids < 0).int() * seq_length
    I = Symbol(integer=True, nonnegative=True, shape=(n,)) # input_ids
    I_quote = Symbol(integer=True, shape=(n,)) # input_ids = torch.gather(input_ids, 1, position_ids)
    Eq << apply(
        Equal(A, Stack[k:n](Bool(I[k] > 0))),
        Equal(P, Stack[k:n](k) + ReducedArgMax(A * Stack[k:n](k)) + 1 - n),
        Equal(P_quote, P + n * Stack[k:n](Bool(P[k] < 0))),
        Equal(I_quote, Stack[k:n](I[P_quote[k]])))

    Eq << Eq[-1].this.lhs.apply(Algebra.ReducedSum.eq.Sum, k)

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedSum.eq.Sum, k)

    Eq << Eq[-1].subs(Eq[3], Eq[2], Eq[1])

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.lhs.args[0].apply(Algebra.Sum.limits.subst.offset, -Eq[-1].find(ReducedArgMax) - 1)

    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Sum.limits.subst.offset, n - Eq[-1].find(ReducedArgMax))




if __name__ == '__main__':
    run()
# created on 2023-11-07
