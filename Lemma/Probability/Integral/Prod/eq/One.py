from util import *


@apply
def apply(self):
    ((((s, t), S[s[t + 1].var]), S[s[t].as_boolean()]), (S[t], S[0], n)), (S[s[1:n + 1].var],) = self.of(Integral[Product[Pr[Conditioned[Equal[Indexed[Symbol, Expr + 1]]]]]])
    return Equal(self, 1)


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Probability, Logic

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    t = Symbol(integer=True) # time step counter
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq.hypothesis = apply(Integral[s[1:n + 1].var](Product[t:n](Pr(s[t + 1] | s[t]))))

    Eq << Eq.hypothesis.subs(n, 0)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Calculus.Integral.limits.pop.Slice)

    Eq << Eq[-1].this.find(Product).apply(Algebra.Prod.eq.Mul.pop)

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.limits.swap)

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.limits.separate)

    Eq << Eq[-1].this.find(Integral[Pr]).apply(Probability.Integral.eq.One.Conditioned)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)
    Eq << Logic.Eq_Ite.of.All_Imp.apply(Eq[-1], n=n, start=0)



if __name__ == '__main__':
    run()
# created on 2023-04-03
