from util import *


@apply
def apply(self):
    expr, *limits = self.of(Expectation)
    if expr.is_Conditioned:
        expr, given = expr.args
    else:
        given = None

    [*args] = expr.of(MatMul)
    scope_variables = self.scope_variables
    from sympy.tensor.indexed import index_intersect
    for i, arg in enumerate(args):
        if index_intersect(arg.random_symbols, scope_variables):
            args[i] = Expectation(arg, *limits, given=given)

    return Equal(self, MatMul(*args))


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Discrete, Tensor

    n = Symbol(integer=True, positive=True)
    A = Symbol(real=True, shape=(n, n))
    s = Symbol(integer=True, random=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    Eq << apply(Expectation(A @ x[:n] | s))

    Eq << Eq[0].this.rhs.find(Sliced).apply(Tensor.Slice.eq.Stack)

    Eq << Eq[-1].this.rhs.find(Expectation).apply(Probability.Expect.Stack.eq.Stack.Expect)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Mul).apply(Probability.Mul.eq.Expect)

    Eq << Eq[-1].this.find(Sum).apply(Probability.Sum.Expect.eq.Expect.Sum)

    Eq << Eq[-1].this.find(Stack).apply(Probability.Stack.Expect.eq.Expect.Stack)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Dot)




if __name__ == '__main__':
    run()
# created on 2023-04-07
