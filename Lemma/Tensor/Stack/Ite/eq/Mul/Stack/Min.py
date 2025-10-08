from util import *


@apply
def apply(self):
    ((i, (j, S[i])), (S[j], S[j < i]), (S[0], S[True])), (S[j], S[0], n), (S[i], S[0], S[n]) = \
    self.of(
        Stack[
            Piecewise[ExprCondPair[Greater],
                      ExprCondPair,
                      ExprCondPair
            ]
        ])
    return Equal(self, (1 - Identity(n)) * Stack[j:n, i:n](Min(i, j)))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Tensor

    n = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Eq << apply(Stack[j:n, i:n](Piecewise((i, j > i), (j, j < i), (0, True))))

    i, j = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], (i, j))

    Eq << Eq[-1].this.find(Min).apply(Algebra.Min.eq.IteLe)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Ite)

    Eq << Eq[-1].this.rhs.simplify(wrt=i)

    Eq << Eq[-1].this.find(LessEqual).reversed

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.eq.Ite)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite, simplify=None)

    Eq << Eq[-1].this.find(Add[Piecewise]).apply(Algebra.Add_Ite.eq.Ite_AddS, simplify=False)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite, simplify=False)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite_Ite.eq.Ite__Ite, index=0)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, -2)

    Eq << Eq[-1].this.lhs.apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not, 0)

    Eq << Eq[-1].this.lhs.find(Equal).reversed





if __name__ == '__main__':
    run()
# created on 2019-10-18
# updated on 2022-04-01
