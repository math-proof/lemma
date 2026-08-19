from util import *


@apply
def apply(self):
    expr, (θ, S[1]) = self.of(Derivative)
    return Equal(self, expr * Derivative[θ](log(expr)))


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=())
    θ = Symbol(real=True, shape=(n,))
    Eq << apply(Derivative[θ](f(θ)))

    Eq << Eq[-1].this.find(Derivative[Log]).doit()

    


if __name__ == '__main__':
    run()
# created on 2023-03-23
