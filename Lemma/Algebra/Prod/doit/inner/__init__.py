from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.doit.inner import doit
    return Equal(self, doit(Product, self))


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    n = 5
    Eq << apply(Product[j:n, i:m](x[i, j]))

    s = Symbol(Stack[i](Product[j:n](x[i, j])))

    Eq << s[i].this.definition

    Eq << Algebra.EqProd.of.Eq.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(Algebra.Prod.eq.Mul.doit)

    Eq << Eq[-2].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()

# created on 2020-03-05
from . import setlimit
