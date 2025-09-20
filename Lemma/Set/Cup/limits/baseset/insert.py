from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


def baseset_insert(self):
    function, *limits = self.args

    * limits, limit = limits
    x, cond = limit
    assert cond.is_bool
    baseset = function.domain_defined(x) & cond.domain_defined(x)
    return self.func(function, *limits, (x, cond, baseset))

@apply
def apply(self):
    assert self.is_Cup
    return Equal(self, baseset_insert(self))


@prove
def prove(Eq):
    from Lemma import Set
    i, j, k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    x, a = Symbol(shape=(n,), integer=True)

    f = Function(etype=dtype.integer)
    h = Function(etype=dtype.real)

    Eq << apply(Cup[j:f(k), k: x[k] > a[i]](h(x[k], j)))

    Eq << Eq[-1].this.rhs.apply(Set.Cup.limits.baseset.delete)

if __name__ == '__main__':
    run()

# created on 2021-02-07
