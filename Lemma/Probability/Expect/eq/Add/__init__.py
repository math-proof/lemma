from util import *


@apply
def apply(self, *, simplify=True):
    expr, *limits = self.of(Expectation)
    if expr.is_Add:
        args = expr.args
        given = None
    else:
        args, given = expr.of(Conditioned[Add])

    args = [Expectation(arg, *limits, given=given) for arg in args]
    if simplify:
        args = [arg.simplify() for arg in args]
    return Equal(self, Add(*args))


@prove
def prove(Eq):
    from Lemma import Probability, Algebra

    n = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(n, n))
    f, g = Function(real=True)
    a, s = Symbol(integer=True, random=True)
    Eq << apply(Expectation[a:θ](f(a) + g(a) | s))

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Sum)

    Eq << Eq[-1].this.find(Expectation).apply(Probability.Expect.eq.Sum)

    Eq << Eq[-1].this.find(Expectation).apply(Probability.Expect.eq.Sum)

    Eq << Eq[-1].this.find(Add[Sum]).apply(Algebra.AddSumS.eq.Sum_Add_Sum)

    Eq << Eq[-1].this.find(Add[Mul]).apply(Algebra.Add.eq.Mul)





if __name__ == '__main__':
    run()
# created on 2023-03-24

# updated on 2023-04-01
from . import Var
