from util import *


@apply
def apply(self, var=None):
    expr = self.of(ReducedMax)
    if expr.is_set:
        fx, *limits = self.of(ReducedMax[Cup[FiniteSet]])
        return Equal(self, Maxima(fx, *limits), evaluate=False)
    if var is None:
        i = self.generate_var(integer=True)
    else:
        i = var
    return Equal(self, Maxima[i:expr.shape[-1]](expr[..., i]), evaluate=False)


@prove(provable=False)
def prove(Eq):
    f = Function(real=True)
    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(ReducedMax({f(x): Element(x, S)}))

    
    


if __name__ == '__main__':
    run()
# created on 2018-12-31
# updated on 2023-10-04
