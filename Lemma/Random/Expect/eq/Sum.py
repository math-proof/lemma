from util import *


def extract(self):
    from sympy.tensor.indexed import index_complement
    expr, *limits = self.of(Expectation)
    
    if expr.is_Conditioned:
        expr, given = expr.args
        if given.is_Equal:
            eqs = [given]
        else:
            eqs = given.of(And)
        
        vars_given = {eq.of(Equal)[0] for eq in eqs}
    else:
        given = None
        vars_given = set()

    values = expr.random_symbols
    values = {*values}
    weights = []
    
    if limits[-1][0].is_random:
        global_weights = []
    else:
        *limits, global_weights = limits
        
    j = 0
    for x, *cond in limits:
        if cond:
            cond, = cond
            if cond.is_Distribution:
                ...
            else:
                weights.append(slice(x, cond))
            
        vars = index_complement(x, vars_given)
        if len(vars) > 1:
            limits = limits[:j] + [(v.var,) for v in vars] + limits[j + 1:]
            j += len(vars)
        elif vars:  
            limits[j] = (x.var,)
            j += 1
        else:
            limits = limits[:j] + limits[j + 1:]
            
        expr = expr._subs(x.surrogate, x.var)
        if expr.is_random:
            expr = expr._subs(x, x.var)
#         assert not expr._has(x), surrogate problem here!

        if x.is_Symbol:
            deletes = set()
            for value in values:
                if (value.is_Sliced or value.is_Indexed) and value.base == x:
                    deletes.add(value)

            values -= deletes
            values.add(x)
            
        elif x.is_Sliced or x.is_Indexed:
            if not any(value.is_Symbol and x.base == value for value in values):
                values.add(x)
        else:
            values.add(x)

    expr *= Pr[tuple([*weights, *global_weights])](*values, given=given)

    for x, *ab in limits:
        if x.is_integer:
            expr = Sum(expr, (x, *ab))
        else:
            expr = Integral(expr, (x, *ab))
            
    return expr

@apply
def apply(self):    
    assert self.limits[-1][0].is_integer
    return Equal(self, extract(self))


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(n, n))
    f = Function(real=True)
    a, s = Symbol(integer=True, random=True)
    Eq << apply(Expectation[a:θ](f(a), given=s))

    
    


if __name__ == '__main__':
    run()
# created on 2023-03-20
# updated on 2023-03-27
