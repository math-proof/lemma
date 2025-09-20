from util import *


@apply
def apply(self):
    expr, *limits = self.of(Variance)
    if expr.is_Conditioned:
        expr, given = expr.args
    else:
        given = None
        
    vars_limited = {v for v, *cond in limits}
    from sympy.tensor.indexed import index_complement
    vars_complement = index_complement(expr.random_symbols, vars_limited)
    for v in vars_complement:
        expr = expr._subs(v, v.surrogate)
        
    if given is not None:
        expr |= given
    return Equal(self,
                 Covariance(expr, expr))

@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x, t = Symbol(real=True, random=True, shape=(n,))
    Eq << apply(Variance(x | t))

    


if __name__ == '__main__':
    run()
# created on 2023-04-14
