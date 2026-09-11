from util import *


@apply
def apply(self):
    expr, *limits = self.of(Expectation)
    for i, (x, *cond) in enumerate(limits):
        if cond:
            if x.is_Indexed or x.is_Sliced or x.is_SlicedIndexed:
                limits[i] = (x.base, *cond)
    return Equal(self, Expectation(expr, *limits))


@prove
def prove(Eq):
    D = Symbol(integer=True, positive=True)
    t = Symbol(integer=True)
    x = Symbol(real=True, shape=(oo,), random=True)
    f = Function(real=True, shape=())
    θ = Symbol(real=True, shape=(D,))
    Eq << apply(Expectation[x[t]:θ](f(x[t])))

    Eq << Eq[-1].this.rhs.simplify()

    


if __name__ == '__main__':
    run()
# created on 2023-04-24
