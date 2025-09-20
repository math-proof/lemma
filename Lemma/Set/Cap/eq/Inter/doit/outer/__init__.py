from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.eq.Add.doit.outer import doit
    return Equal(self, doit(Cap, self))


@prove
def prove(Eq):
    from Lemma import Set
    x = Symbol(etype=dtype.real, shape=(oo, oo))
    i, j = Symbol(integer=True)
    f = Function(integer=True)

    n = 5
    Eq << apply(Cap[j:f(i), i:n](x[i, j]))

    s = Symbol(Stack[i](Cap[j:f(i)](x[i, j])))

    Eq << s[i].this.definition

    Eq << Set.EqCap.of.Eq.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.lhs.apply(Set.Cap.eq.Inter.doit).reversed

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition


if __name__ == '__main__':
    run()

# created on 2021-02-01
from . import setlimit
