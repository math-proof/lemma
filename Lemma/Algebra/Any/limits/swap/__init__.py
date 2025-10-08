from util import *


@apply
def apply(self, i=0, j=1):
    from Lemma.Algebra.Sum.limits.swap import rewrite
    return rewrite(Any, self, i, j)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    a, b, c, d = Symbol(real=True, positive=True)
    x, y = Symbol(real=True)
    f, g = Function(bool=True)
    Eq << apply(Any[x:a:b, y:c:d](f(x) & g(x, y)))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Any.of.Any.limits.swap, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.given.Any.limits.swap, simplify=None)



if __name__ == '__main__':
    run()
# created on 2023-07-02


# updated on 2023-11-12
from . import intlimit
from . import subst
