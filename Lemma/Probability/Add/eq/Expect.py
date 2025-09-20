from util import *


@apply
def apply(self, *, simplify=True):
    [*args] = self.of(Add)
    for i, arg in enumerate(args):
        if arg.is_Expectation:
            expr, *limits = arg.args
            vars = arg.variables
            if expr.is_Conditioned:
                expr, given = expr.args
            else:
                given = None
            break
    else :
        return

    for arg in args[i + 1:]:
        if arg.is_Expectation:
            from sympy.tensor.indexed import index_intersect
            assert not index_intersect(arg.variables, vars)

    args[i] = expr
    expr = Add(*args)
    return Equal(self, Expectation(expr, *limits, given=given), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Probability

    n = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(n, n))
    f, g = Function(real=True)
    a, s, b = Symbol(integer=True, random=True)
    Eq << apply(Expectation[a:θ](f(a) | s) + g(b))

    Eq << Eq[0].this.rhs.apply(Probability.Expect.eq.Add)






if __name__ == '__main__':
    run()
# created on 2023-04-12
