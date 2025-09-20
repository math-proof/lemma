from util import *


def doit(Sum, self):
    xi, *limits, limit = self.of(Sum)
    i, a, b = limit.of(Tuple)
    assert i.is_integer

    diff = b - a
    assert diff == int(diff)

    sgm = Sum.identity(xi)

    for t in range(diff):
        _limits = []
        for (j, *ab) in limits:
            _limits.append((j, *(c._subs(i, a + t) for c in ab)))

        sgm = Sum.operator(sgm, Sum(xi._subs(i, a + t), *_limits))
    return sgm


@apply
def apply(self):
    return Equal(self, doit(Sum, self))


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    f = Function(integer=True)

    n = 5
    Eq << apply(Sum[j:f(i), i:n](x[i, j]))

    s = Symbol(Stack[i](Sum[j:f(i)](x[i, j])))

    Eq << s[i].this.definition

    Eq << Algebra.EqSumS.of.Eq.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.doit).reversed

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition


if __name__ == '__main__':
    run()

# created on 2019-02-22
from . import setlimit
