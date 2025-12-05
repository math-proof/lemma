from util import *


@apply
def apply(self):
    expr, *limits = self.of(Expectation)
    if expr.is_Conditioned:
        expr, given = expr.args
    else:
        given = None

    expr = expr.of(ReducedSum)

    expr = self.func(expr, *limits, given=given)
    return Equal(self, ReducedSum(expr))


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Vector

    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    s = Symbol(integer=True, random=True)
    x = Symbol(real=True, random=True, shape=(n,))
    Eq << apply(Expectation(ReducedSum(f(x)) | s))

    Eq << Eq[0].this.find(ReducedSum).apply(Vector.Sum.eq.Sum_Get)

    Eq << Eq[-1].this.find(ReducedSum).apply(Vector.Sum.eq.Sum_Get)

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.Sum.eq.Sum.Expect)


if __name__ == '__main__':
    run()
# created on 2023-04-10
