from util import *


def rewrite(Sum, self, simplify=True):
    (expr, *limits_e), *limits_s = self.of(Sum[Expectation])
    vars_s = [v for v, *_ in limits_s]

    if expr.is_Conditioned:
        expr, given = expr.args
        assert not given.has(*vars_s)
    else:
        given = None

    expr_s = Sum(expr, *limits_s)
    if simplify:
        expr_s = expr_s.simplify()

    for i, (v, *cond) in enumerate(limits_e):
        if v.has(*vars_s):
            v = v.expand_indices(limits_s, expr=expr)
            limits_e[i] = (v, *cond)
    rhs = Expectation(expr_s, *limits_e, given=given)
    assert self.random_symbols == rhs.random_symbols
    return rhs

@apply
def apply(self, *, simplify=True):
    return Equal(self, rewrite(Sum, self, simplify))


@prove
def prove(Eq):
    from Lemma import Probability

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f = Function(real=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    s = Symbol(real=True, random=True)
    Eq << apply(Sum[k:n](Expectation(f(x[k]) | s)))

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.Sum.eq.Sum.Expect)




if __name__ == '__main__':
    run()
# created on 2023-04-02
