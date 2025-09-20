from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.doit.inner import doit
    return Equal(self, doit(Cap, self))


@prove
def prove(Eq):
    from Lemma import Set, Algebra
    x = Symbol(etype=dtype.real, shape=(oo, oo))
    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    n = 5
    Eq << apply(Cap[j:n, i:m](x[i, j]))

    s = Symbol(Stack[i](Cap[j:n](x[i, j])))

    Eq << s[i].this.definition

    Eq << Set.EqCap.of.Eq.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(Set.Cap.eq.Inter.doit)

    Eq << Eq[-2].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()

# created on 2021-01-20
from . import setlimit
