from util import *


def rewrite(self, *vars):
    given = S.true
    for v in vars:
        given &= v.surrogate

    expr, *limits_inner = self.of(Expectation)
    if expr.is_Conditioned:
        expr, given_outer = expr.args
        given &= given_outer
    else:
        given_outer = None

    vars_given = set()
    for x in expr.random_symbols:
        for v in vars:
            if v.index_contains(x):
                vars_given.add(x)

    from std import deleteIndices
    limits_weighted = []
    def process(limit):
        x, *cond = limit
        if x in vars_given:
            if cond:
                limits_weighted.append(limit)
            return True

    deleteIndices(limits_inner, process)

    if limits_weighted:
        limits_outer = []
        for v in vars:
            for x, *cond in limits_weighted:
                if v.index_contains(x):
                    limit = (v, *cond)
                    break
            else:
                limit = (v,)

            limits_outer.append(limit)

        for x, *cond in limits_weighted:
            if x.is_Indexed:
                x = x.base
            limits_inner.append((x, *cond))
    else:
        limits_outer = []

    rhs = Expectation(Expectation(expr | given, *limits_inner), *limits_outer, given=given_outer)
    assert rhs.random_symbols == self.random_symbols
    return rhs

@apply
def apply(self, *vars):
    return Equal(self, rewrite(self, *vars))


@prove
def prove(Eq):
    from Lemma import Probability

    # this is the proof of the law of iterated expectations
    # https://en.wikipedia.org/wiki/Law_of_total_expectation
    x, y, z = Symbol(real=True, random=True)
    f = Function(real=True, shape=())
    Eq << apply(Expectation(f(x)), y, z)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.law_of_total_expectation)





if __name__ == '__main__':
    run()
# created on 2023-04-01
# updated on 2023-04-22
