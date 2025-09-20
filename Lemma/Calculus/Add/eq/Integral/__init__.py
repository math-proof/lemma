from util import *


@apply
def apply(self):
    from Lemma.Algebra.AddSumS.eq.Sum_Add_Sum import piece_together
    return Equal(self, piece_together(Integral, self))


@prove
def prove(Eq):
    from Lemma import Calculus

    x, a, b = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Integral[x:a:b](f(x)) + Integral[x:a:b](g(x)))


    Eq << Eq[0].this.rhs.apply(Calculus.Integral.eq.Add)



if __name__ == '__main__':
    run()

# created on 2020-06-06
# updated on 2023-06-02
from . import concat
