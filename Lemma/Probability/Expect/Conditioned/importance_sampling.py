from util import *


@apply
def apply(self, *new_weights):
    (fx, given), *limits = self.of(Expectation[Conditioned])
    random_symbols = fx.random_symbols
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

        vars = [v for v in random_symbols if x.index_contains(v)]
        if len(vars) == 1:
            x, = vars

        conds.append(Equal(x, x.surrogate))

    conds = And(*conds)
    return Equal(self,
                 Expectation(fx * Pr(conds, *limits_weighted, given=given) / Pr(conds, *new_limits_weighted, given=given), *limits, given=given))

@prove
def prove(Eq):
    from Lemma import Probability

    b, D = Symbol(integer=True, positive=True)
    # D denotes the size of the trainable weights
    s = Symbol(real=True, shape=(b,), random=True)
    x = Symbol(integer=True, random=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    f = Function(real=True, shape=())
    Eq << apply(Expectation[x:θ](f(x) | s), θ_quote)

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Sum)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.eq.Sum)




if __name__ == '__main__':
    run()
# created on 2023-04-03
