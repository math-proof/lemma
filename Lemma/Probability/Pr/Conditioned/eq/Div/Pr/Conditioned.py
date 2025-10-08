from util import *


@apply
def apply(self, pivot=-1):
    y, given = self.of(Pr[Conditioned[And]])
    x, z = std.array_split(given, pivot)
    x = And(*x)
    z = And(*z)
    return Equal(self, Pr(x & y, given=z) / Pr(x, given=z))


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Bool

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Pr(y | x & z))

    Eq << Bool.Cond.given.Imp.domain_defined.apply(Eq[0])

    Eq << Bool.Imp_And.given.Imp_And.And.apply(Eq[-1], -1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne_0.Eq.given.And.Mul)

    Eq << Eq[-1].this.lhs.args[1].apply(Probability.Eq.Pr.Conditioned.eq.Mul.Pr.Conditioned.of.Ne_0.bayes, x, y)

    Eq << Eq[-1].this.rhs.reversed





if __name__ == '__main__':
    run()
# created on 2023-10-13
# updated on 2023-10-14
