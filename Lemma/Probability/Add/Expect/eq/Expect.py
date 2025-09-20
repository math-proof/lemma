from util import *

def try_insert(limits, limit_curr):
    x_curr, *cond_curr = limit_curr
    for i, limit_prev in enumerate(limits):
        x_prev, *cond_prev = limit_prev

        if x_prev.index_contains(x_curr):
            return

        if x_curr.index_contains(x_prev):
            if cond_curr:
                raise
            else:
                if cond_prev:
                    raise
                else:
                    limits[i] = limit_curr
            return

    limits.append(limit_curr)

@apply
def apply(self, *, simplify=True):
    [*args] = self.of(Add)
    exprs = []
    limits = []
    given = None
    for arg in args:
        if arg.is_Expectation:
            expr, *limits_curr = arg.args
            coeff = 1
        else:
            coeff, (expr, *limits_curr) = arg.of(Expr * Expectation)
        if expr.is_Conditioned:
            expr, _given = expr.args
            if given is None:
                given = _given
            else:
                assert given == _given
        else:
            assert given is None

        for limit_curr in limits_curr:
            try_insert(limits, limit_curr)

        exprs.append(expr * coeff)

    expr = Add(*exprs)
    return Equal(self, Expectation(expr, *limits, given=given), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Probability

    n = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(n, n))
    f, g = Function(real=True)
    a, s, b = Symbol(integer=True, random=True)
    Eq << apply(Expectation[a:θ](f(a) | s) + Expectation[a:θ](g(a) | s))

    Eq << Eq[0].this.rhs.apply(Probability.Expect.eq.Add)


if __name__ == '__main__':
    run()
# created on 2023-04-13
