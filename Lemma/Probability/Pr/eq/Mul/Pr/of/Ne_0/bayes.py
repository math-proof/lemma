from util import *


@apply
def apply(eq, *expr, spread_weight=False):
    assert expr
    condition = And(*(Equal(y, y.var) for y in expr))

    given_probability = eq.of(Unequal[0])
    cond = given_probability.of(Pr)

    if isinstance(cond, tuple):
        cond, weight = cond
        random_symbols = [v for v in cond.random_symbols if not v.is_Surrogate]
        if spread_weight:
            limits = [weight]
        else:
            limits = [(v, *weight) for v in random_symbols]
    else:
        limits = []

    return Equal(Pr(cond & condition, *limits), given_probability * Pr(condition, given=cond, *limits))


@prove
def prove(Eq):
    from Lemma import Probability

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Pr(y), 0), x)

    Eq << Eq[-1].this.find(Pr[Conditioned]).apply(Probability.Pr.eq.Div.Pr.bayes)


if __name__ == '__main__':
    run()

# created on 2020-12-09
