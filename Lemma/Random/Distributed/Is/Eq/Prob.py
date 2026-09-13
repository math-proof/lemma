from util import *


@apply
def apply(self, var=None):
    expr, dist = self.of(Distributed)
    if var is None:
        if expr.is_symbol:
            var = expr.var
        else:
            var = dist.generate_var(shape=expr.shape, **expr.dtype.dict)

    return Equal(Pr(Equal(expr, var)), dist(var), evaluate=False)


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True, random=True)
    μ = Symbol(real=True)
    σ = Symbol(positive=True)
    Eq << apply(Distributed(x, NormalDistribution(μ, σ)))

    


if __name__ == '__main__':
    run()
# created on 2023-04-10
