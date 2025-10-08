from util import *


@apply
def apply(self):
    (((s, k), S[s[k].var]), S[s[:k].as_boolean()]), (S[k], S[0], n) = self.of(Product[Pr[Conditioned[Equal[Indexed]]]])
    return Equal(self, Pr(s[:n]), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Bool

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True)  # states / observation
    k = Symbol(integer=True)  # time step counter
    n = Symbol(integer=True, nonnegative=True, given=False)  # total time step
    Eq << apply(Product[k:n](Pr(s[k] | s[:k])))


    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.lhs.apply(Algebra.Prod.eq.Mul.pop)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.find(Pr[Conditioned]).apply(Probability.Pr.eq.Div.Pr.bayes)

    Eq << Eq[-1].this.find(Equal & Equal).apply(Algebra.Eq.Eq.Is.Eq.concat)

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq << Bool.Eq_Ite.of.All_Imp.apply(Eq[-1], n=n, start=0)




if __name__ == '__main__':
    run()
# created on 2023-04-08
