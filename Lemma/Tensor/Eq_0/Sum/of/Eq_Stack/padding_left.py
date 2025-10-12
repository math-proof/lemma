from util import *


@apply
def apply(eq_A):
    ((I, k), limit), A = eq_A.of(Equal[Stack[Bool[Indexed > 0]]])
    assert I >= 0
    return Equal(Sum[k:ReducedArgMax(A)](I[k]), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Int, Int, Nat

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True) # seq_length
    A = Symbol(integer=True, shape=(n,)) # attention_mask = (input_ids > 0).int()
    I = Symbol(integer=True, nonnegative=True, shape=(n,)) # input_ids
    Eq << apply(Equal(A, Stack[k:n](Bool(I[k] > 0))))

    m = Symbol(Eq[-1].find(ReducedArgMax))
    Eq.m_def = m.this.definition

    Eq << Algebra.All.Gt.of.Eq_ReducedArgMax.apply(Eq.m_def, k)

    Eq << Eq[0][m]


    Eq << Eq[-2].subs(Eq[-1])
    Eq << Eq[-1].this.expr.apply(Algebra.Gt.of.Gt.relax, upper=1)
    Eq << Eq[0][k]
    Eq << Eq[-2].subs(Eq[-1])
    Eq << Eq[-1].this.expr.apply(Algebra.Le_Sub_1.of.Lt)
    Eq << Eq[-1].this.expr.apply(Nat.Eq_0.of.Le_0)
    Eq << Eq[-1].this.expr.apply(Algebra.Cond.of.Eq_0.invert)
    Eq << Eq[-1].this.expr.apply(Nat.Eq_0.of.Le_0)
    Eq << Eq[-1].subs(Eq.m_def)
    Eq << Algebra.EqSumS.of.All_Eq.apply(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-11-05
