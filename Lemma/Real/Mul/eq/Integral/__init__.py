from util import *


@apply
def apply(self):
    from Lemma.Finset.Mul_Sum.eq.Sum_Mul import rewrite
    return Equal(self, rewrite(Integral, self))


@prove
def prove(Eq):
    x, y, a, b, c, d = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x:a:b](f(x)) * y)

    Eq << Eq[-1].this.rhs.simplify()




if __name__ == '__main__':
    run()

# created on 2020-06-06
# updated on 2023-03-28

from . import as_multiple_limits
