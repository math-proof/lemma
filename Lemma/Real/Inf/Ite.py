from util import *


@apply
def apply(self):
    expr, *limits = self.of(Inf)

    return Equal(self, self.func(Piecewise((expr, self.limits_cond), (oo, True)), *((x,) for x, *_ in limits)))


@prove
def prove(Eq):
    A = Symbol(etype=dtype.integer)
    x = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Inf[x:A](f(x)))
    
    Eq << Eq[0].this.rhs.simplify()


if __name__ == '__main__':
    run()
# created on 2023-04-23
