from util import *


@apply
def apply(self, *, simplify=True):
    expr, *limits_e = self.of(ReducedSum[Expectation])
    if expr.is_Conditioned:
        expr, given = expr.args
    else:
        given = None

    expr_s = ReducedSum(expr)
    rhs = Expectation(expr_s, *limits_e, given=given)
    assert self.random_symbols == rhs.random_symbols

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Probability

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f = Function(real=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    s = Symbol(real=True, random=True)
    Eq << apply(ReducedSum(Expectation(f(x) | s)))

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.ReducedSum.eq.ReducedSum.Expect)




if __name__ == '__main__':
    run()
# created on 2023-04-10
