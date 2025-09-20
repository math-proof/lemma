from util import *



def limits_delete(self):
    function, *limits = self.args

    * limits, limit = limits
    x, domain = limit.coerce_setlimit()

    assert function.domain_defined(x) in domain
    return self.func(function, *limits, (x,))

@apply
def apply(self):
    assert self.is_Sum
    return Equal(self, limits_delete(self))


@prove
def prove(Eq):
    from Lemma import Algebra
    i, j = Symbol(integer=True)
    k = Symbol(integer=True, positive=True)
    x = Symbol(shape=(k,), integer=True)

    f = Function(etype=dtype.integer)
    h = Function(real=True)

    Eq << apply(Sum[j:f(i), i:k](h(x[i], j)))

    s = Symbol(Sum[j:f(i)](h(x[i], j)))
    Eq << s.this.definition

    Eq << Algebra.EqSumS.of.Eq.apply(Eq[-1], (i, 0, k))

    Eq << Eq[-1].this.lhs.expr.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2019-11-02
