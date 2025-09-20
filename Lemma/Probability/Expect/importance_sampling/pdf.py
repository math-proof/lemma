from util import *


@apply
def apply(self, *new_weights):
    fx, *limits = self.of(Expectation)
    new_weights = [*new_weights]
    limits_weighted = []
    new_limits_weighted = []

    conds = []
    for i, (x, *weights) in enumerate(limits):
        if weights:
            new_weight = new_weights.pop(0)
            if isinstance(new_weight, (list, tuple)):
                limits[i] = (x, *new_weight)
            else:
                limits[i] = (x, new_weight)

            limits_weighted.append((x, *weights))
            new_limits_weighted.append(limits[i])
        conds.append(Equal(x, x.surrogate))

    conds = And(*conds)
    return Equal(self,
                 Expectation(fx * Pr(conds, *limits_weighted) / Pr(conds, *new_limits_weighted), *limits))

@prove
def prove(Eq):
    from Lemma import Probability

    D = Symbol(integer=True, positive=True)
    # D denotes the size of the trainable weights
    x = Symbol(real=True, random=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    f = Function(real=True, shape=())
    Eq << apply(Expectation[x:θ](f(x)), θ_quote)

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.eq.Integral)




if __name__ == '__main__':
    run()
# created on 2023-03-25
