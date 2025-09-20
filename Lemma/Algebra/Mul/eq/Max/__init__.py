from util import *



@apply
def apply(self, evaluate=False):
    from Lemma.Algebra.Mul.eq.Min import extract
    rhs = extract(Max, self)

    return Equal(self, rhs, evaluate=evaluate)


@prove
def prove(Eq):
    from Lemma import Algebra

    t = Symbol(real=True, positive=True)
    x, y = Symbol(real=True)
    Eq << apply(t * Max(x, y))
    Eq << Eq[0].this.rhs.apply(Algebra.Max.eq.Mul)


if __name__ == '__main__':
    run()
# created on 2020-01-29
from . import of
