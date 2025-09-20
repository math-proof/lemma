from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


def baseset_delete(self):
    function, *limits = self.args

    * limits, limit = limits
    x, cond, baseset = limit
    assert cond.is_bool
    assert baseset.is_set

    assert function.domain_defined(x) & cond.domain_defined(x) in baseset
    return self.func(function, *limits, (x, cond))


@apply
def apply(self):
    assert self.is_Cup
    return Equal(self, baseset_delete(self))


@prove
def prove(Eq):
    from Lemma import Set
    i, j, k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    x, a = Symbol(shape=(n,), integer=True)

    f = Function(etype=dtype.integer)
    h = Function(etype=dtype.real)

    Eq << apply(Cup[j:f(k), k: x[k] > a[i]: Range(n)](h(x[k], j)))

    s = Symbol(Cup[j:f(k)](h(x[k], j)))
    Eq << s.this.definition

    Eq << Set.EqCupS.of.All_Eq.fin.apply(Eq[-1], (k, x[k] > a[i], Range(n)))

    Eq << Eq[-1].this.lhs.expr.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-02-07
