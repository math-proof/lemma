from util import *


@apply
def apply(self):
    assert self.is_Probability
    return GreaterEqual(self, 0, evaluate=False)


@prove
def prove(Eq):
    D, m = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, integer=True, shape=(m,))
    Eq << apply(Pr[θ](x))

    Eq << Eq[0].this.lhs.simplify()

    


if __name__ == '__main__':
    run()
# created on 2023-04-04
