from util import *


@apply
def apply(eq_A):
    ((I, k), limit), A = eq_A.of(Equal[Stack[Bool[Indexed > 0]]])
    assert I >= 0
    n, = A.shape
    return Equal(Sum[k:ReducedArgMax(A * Stack[k:n](k)) + 1:n](I[k]), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Int, Nat, Finset

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True) # seq_length
    A = Symbol(integer=True, shape=(n,)) # attention_mask = (input_ids > 0).int()
    I = Symbol(integer=True, nonnegative=True, shape=(n,)) # input_ids
    Eq << apply(Equal(A, Stack[k:n](Bool(I[k] > 0))))

    m = Symbol(Eq[-1].find(ReducedArgMax))
    Eq.m_def = m.this.definition

    Eq << Algebra.All.Ge.of.Eq_ReducedArgMax.apply(Eq.m_def, k, simplify=None)

    Eq << Eq[0][m] * m

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Set.AllIn_SDiff.of.All.apply(Eq[-1], Range(m + 1, n))

    Eq << LessEqual(Eq[-1].find(Bool), 1, plausible=True)

    Eq << Eq[-1] * m

    Eq << Algebra.All.And.of.Cond.All.apply(Eq[-1], Eq[-3], simplify=None)

    Eq << Eq[-1].this.expr.apply(Nat.Ge.of.Le.Ge)

    Eq << Eq[0][k] * k
    Eq << Eq[-2].subs(Eq[-1])
    Eq << Algebra.All.And.of.All.apply(Eq[-1])
    Eq << Eq[-1].this.find(Element).apply(Set.Ge.of.In_Ico)
    Eq << Eq[-1].this.find(GreaterEqual[2]).apply(Algebra.Gt_0.of.Ge, ret=True, simplify=None)
    Eq << Eq[-1].this.find(Greater).apply(Algebra.Div.gt.Zero.of.Gt_0)
    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.GeMul.of.Gt_0.Ge, ret=0)
    Eq << Eq[-1].this.find(GreaterEqual).apply(Nat.Gt_Sub_1.of.Ge)
    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.GtMul.of.Gt_0.Gt)
    Eq << Eq[-1].this.expr.apply(Algebra.Lt.of.Lt.Ge)
    Eq << Eq[-1].this.expr.apply(Nat.Le_Sub_1.of.Lt)
    Eq << Eq[-1].this.expr.apply(Nat.Eq_0.of.Le_0)
    Eq << Eq[-1].this.expr.apply(Algebra.Cond.of.Eq_0.invert)
    Eq << Eq[-1].this.expr.apply(Nat.Eq_0.of.Le_0)
    Eq << Finset.Sum.of.All_Eq.apply(Eq[-1])
    Eq << Eq[-1].subs(Eq.m_def)



if __name__ == '__main__':
    run()
# created on 2023-11-05
