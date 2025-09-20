from util import *


def rewrite(Sum, self, *sym):
    conds = self.of(Pr)
    vars = []
    if conds.is_Conditioned:
        conds, given = conds.of(Conditioned)
    else:
        given = None

    limits = []
    for s in sym:
        conds &= s
        limits.append((s.var,))

    expr = Pr(conds, given=given)

    for limit in limits:
        if limit[0].is_integer:
            expr = Sum(expr, limit)
        else:
            expr = Integral(expr, limit)
    return expr

@apply
def apply(self, y):
    assert y.is_integer
    return Equal(self, rewrite(Sum, self, y))


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Logic

    x, y = Symbol(integer=True, random=True)
    Eq << apply(Pr(x), y)

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[0], cond=Equal(Pr(x), 0))

    Eq << Eq[-1].this.lhs.apply(Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes, y)

    Eq << Logic.Imp.given.Imp.subst.apply(Eq[-1])

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1].this.find(Sum).apply(Probability.Sum.eq.One.Conditioned)

    Eq << Logic.Imp.given.Imp.subst.apply(Eq[1])

    Eq << Eq[-1].this.rhs.reversed

    Eq << Eq[-1].this.lhs.apply(Probability.Eq_0.of.Eq_0.joint, y)

    Eq << Logic.Imp.given.Imp.subst.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-03-30
