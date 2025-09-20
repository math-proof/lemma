from util import *


def limits_insert(self):
    function, *limits = self.args

    * limits, limit = limits
    x = limit[0]
    domain_defined = function.domain_defined(x)

    if len(limit) == 1:
        limit = (x, domain_defined)
    elif len(limit) == 2:
        cond = limit[1]
        assert cond.is_bool
        limit = (x, cond, domain_defined)
    else:
        _, a, b = limit
        limit = (x, x.range(a, b) & domain_defined)

    return self.func(function, *limits, limit)

@apply
def apply(self):
    assert self.is_Sum
    return Equal(self, limits_insert(self), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra
    i, j = Symbol(integer=True)
    k = Symbol(integer=True, positive=True)
    x = Symbol(shape=(k,), integer=True)

    f = Function(etype=dtype.integer)
    h = Function(real=True)

    Eq << apply(Sum[j:f(i), i](h(x[i], j)))

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.domain_defined.delete)

if __name__ == '__main__':
    run()

# created on 2019-11-04

from . import delete
