from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.doit.inner import doit
    return Equal(self, doit(Cup, self))


@prove
def prove(Eq):
    from Lemma import Set
    x = Symbol(etype=dtype.real, shape=(oo, oo))
    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    n = 5
    Eq << apply(Cup[j:n, i:m](x[i, j]))

    s = Symbol(Stack[i](Cup[j:n](x[i, j])))

    Eq << s[i].this.definition

    Eq << Set.EqCupS.of.All_Eq.fin.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(Set.Cup.eq.Union.doit)

    Eq << Eq[-2].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()

# created on 2021-02-06
from . import setlimit
