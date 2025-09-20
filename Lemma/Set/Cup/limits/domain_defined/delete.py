from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.limits.domain_defined.delete import limits_delete
    assert self.is_Cup
    return Equal(self, limits_delete(self))


@prove
def prove(Eq):
    from Lemma import Set
    i, j = Symbol(integer=True)
    k = Symbol(integer=True, positive=True)
    x = Symbol(shape=(k,), integer=True)

    f = Function(etype=dtype.integer)
    h = Function(etype=dtype.real)

    Eq << apply(Cup[j:f(i), i:k](h(x[i], j)))

    s = Symbol(Cup[j:f(i)](h(x[i], j)))
    Eq << s.this.definition

    Eq << Set.EqCupS.of.All_Eq.fin.apply(Eq[-1], (i, 0, k))

    Eq << Eq[-1].this.lhs.expr.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2020-07-24
