from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.limits.domain_defined.delete import limits_delete
    assert self.is_Cap
    return Equal(self, limits_delete(self))


@prove
def prove(Eq):
    from Lemma import Set
    i, j = Symbol(integer=True)
    k = Symbol(integer=True, positive=True)
    x = Symbol(shape=(k,), integer=True)

    f = Function(etype=dtype.integer)
    h = Function(etype=dtype.real)

    Eq << apply(Cap[j:f(i), i:k](h(x[i], j)))

    s = Symbol(Cap[j:f(i)](h(x[i], j)))
    Eq << s.this.definition

    Eq << Set.EqCap.of.Eq.apply(Eq[-1], (i, 0, k))

    Eq << Eq[-1].this.lhs.expr.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-01-18
