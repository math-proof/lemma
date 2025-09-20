from util import *


@apply
def apply(self):
    [*args] = self.of(MatMul)
    for i, expect in enumerate(args):
        if expect.is_Expectation:
            break
    else :
        return

    expr, *limits = expect.args

    if expr.is_Conditioned:
        expr, given = expr.args
    else:
        given = None

    scope_variables = expect.scope_variables
    args[i] = S.One
    from sympy.tensor.indexed import index_intersect
    for arg in args:
        assert not index_intersect(arg.random_symbols, scope_variables)

    args[i] = expr
    expr = MatMul(*args)
    return Equal(self, Expectation(expr, *limits, given=given))


@prove
def prove(Eq):
    from Lemma import Probability

    n = Symbol(integer=True, positive=True)
    A = Symbol(real=True, shape=(n, n))
    s = Symbol(integer=True, random=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    Eq << apply(A @ Expectation(x[:n] | s))


    Eq << Eq[0].this.rhs.apply(Probability.Expect.eq.Dot)



if __name__ == '__main__':
    run()
# created on 2023-04-07
