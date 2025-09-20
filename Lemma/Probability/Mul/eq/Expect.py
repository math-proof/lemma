from util import *


@apply
def apply(self):
    (expr, *limits), *constant = self.of(Mul[Expectation])
    constant = Mul(*constant)
    if expr.is_Conditioned:
        expr, given = expr.args
    else:
        given = None

    return Equal(self, Expectation(constant * expr, *limits, given=given))


@prove
def prove(Eq):
    from Lemma import Probability

    n = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(n, n))
    f, g = Function(real=True)
    a, s = Symbol(integer=True, random=True)
    b = Symbol(integer=True)
    Eq << apply(g(b) * Expectation[a:θ](f(a) | s))

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.eq.Mul)



if __name__ == '__main__':
    run()
# created on 2023-04-02
