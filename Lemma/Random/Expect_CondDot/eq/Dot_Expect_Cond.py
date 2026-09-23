from util import *


@apply
def apply(self):
    expr, *limits = self.of(Expectation)
    args, given = expr.of(Conditioned[MatMul])

    scope_variables = self.scope_variables
    from sympy.tensor.indexed import index_intersect
    args = [*args]
    for i, arg in enumerate(args):
        if index_intersect(arg.random_symbols, scope_variables):
            args[i] = Expectation(arg, *limits, given=given)

    return Equal(self, MatMul(*args))


@prove
def prove(Eq):
    from Lemma import Random, Tensor

    n = Symbol(integer=True, positive=True)
    A = Symbol(real=True, shape=(n, n))
    s = Symbol(integer=True, random=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    Eq << apply(Expectation(A @ x[:n] | s))

    Eq << Eq[0].this.rhs.find(Sliced).apply(Tensor.GetSlice.As.Stack.of.LeAdd)

    Eq << Eq[-1].this.rhs.find(Expectation).apply(Random.Expect_Stack.eq.Stack_Expect)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-1].this.find(Mul).apply(Random.Mul_Expect.eq.Expect_Mul)

    Eq << Eq[-1].this.find(Sum).apply(Random.Sum_Expect.eq.Expect_Sum)

    Eq << Eq[-1].this.find(Stack).apply(Random.Stack_Expect.eq.Expect_Stack)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack_Sum_MulGetS.eq.Dot)


if __name__ == '__main__':
    run()
# created on 2026-09-23
# based on Random.Expect_Dot.eq.Dot_Expect
