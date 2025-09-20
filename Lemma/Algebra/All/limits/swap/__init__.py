from util import *


@apply
def apply(self, i=0, j=1):
    from Lemma.Algebra.Sum.limits.swap import rewrite
    return rewrite(All, self, i, j)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, b, c, d = Symbol(real=True, positive=True)
    x, y = Symbol(real=True)
    f, g = Function(bool=True)
    Eq << apply(All[x:a:b, y:c:d](f(x) & g(x, y)))

    Eq << Eq[0].this.lhs.apply(Algebra.All.Is.Or)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.Is.Or)


if __name__ == '__main__':
    run()
# created on 2023-07-02


from . import intlimit
from . import subst
