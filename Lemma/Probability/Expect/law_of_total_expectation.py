from util import *


def rewrite(self):
    expr, *limits_outer = self.of(Expectation)
    if expr.is_Conditioned:
        expr, given_outer = expr.args
        if given_outer.is_Equal:
            cond_outer = {given_outer}
        else:
            cond_outer = given_outer.of(And)

        vars_given_dict = {}
        for eq in cond_outer:
            x, x_var = eq.of(Equal)
            if x_var.is_Surrogate:
                x_var = x_var.arg.var
            vars_given_dict[x] = x_var
    else:
        given_outer = None
        vars_given_dict = {}

    ((expr, given), *limits_inner) = expr.of(Expectation[Conditioned])
    vars_inner = {v for v, *_ in limits_inner if v.is_random}
    vars_outer = {v for v, *_ in limits_outer}

    assert all(v.is_random for v in vars_outer)

    if given.is_Equal:
        conds = [given]
    else:
        conds = given.of(And)

    vars_given = set()
    for cond in conds:
        x, x_var = cond.of(Equal)
        if x_var.is_Surrogate:
            vars_given.add(x)
            assert x_var == x.surrogate
            assert x in vars_outer
        else:
            assert x_var == vars_given_dict[x]

    vars_weighted = set()
    assert vars_given & vars_outer == vars_given
    for var in vars_outer - vars_given:
        assert not expr._has(var)
        vars_weighted.add(var)

    rest = set()
    for v in expr.random_symbols:
        if v in vars_given:
            rest.add(v)
        elif v in vars_given_dict:
            continue
        elif not any(V.index_contains(v) for V in vars_inner):
            rest.add(v)

    assert not rest - vars_given

    limits = []
    for v in rest:
        for V, *_ in limits_inner:
            if V.index_contains(v):
                break
        else:
            limits.append((v,))
    limits = limits_inner + limits

    limits_weights = self.limits_weights

    if not any(cond for v, *cond in limits) and expr.random_symbols == {v for v, in limits}:
        if not limits_weights:
            limits = []
    else:
        for i, (x, *ab) in enumerate(limits):
            if x.is_random and not expr._has(x) and ab and x not in vars_weighted:
                for limit in limits_outer:
                    _x, *_ab = limit
                    if _x.is_random and _x._has(x) and _ab != ab:
                        if x.index_contains(_x):
                            limit = (x, *_ab)
                        limits[i] = limit
                        break

    vars = {v for v, *_ in limits}
    if (ret := std.deleteIndices(limits_weights, lambda limit: limit[0] in vars)) is not None:
        limits_weights = ret

    rhs = Expectation(expr, *limits, *limits_weights, given=given_outer)
    assert rhs.random_symbols == self.random_symbols
    return rhs

@apply
def apply(self):
    return Equal(self, rewrite(self))


@prove
def prove(Eq):
    from Lemma import Probability, Calculus

    x, y = Symbol(real=True, random=True)
    f = Function(real=True)
    Eq << apply(Expectation(Expectation(f(x, y) | y.surrogate)))

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].this.lhs.find(Expectation).apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].this.find(Mul[Integral]).apply(Calculus.Mul.eq.Integral)

    Eq << Eq[-1].this.find(Pr[Conditioned]).apply(Probability.Pr.eq.Div.Pr.bayes)

    Eq << Eq[-1].this.lhs.apply(Probability.Integral.eq.Expect)





if __name__ == '__main__':
    run()
# created on 2023-03-31
# updated on 2023-04-22
