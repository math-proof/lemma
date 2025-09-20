from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.limits.domain_defined.delete import limits_delete
    assert self.is_Product
    return Equal(self, limits_delete(self))


@prove
def prove(Eq):
    from Lemma import Algebra
    i, j = Symbol(integer=True)
    k = Symbol(integer=True, positive=True)
    x = Symbol(shape=(k,), integer=True)

    f = Function(etype=dtype.integer)
    h = Function(real=True)

    Eq << apply(Product[j:f(i), i:k](h(x[i], j)))

    s = Symbol(Product[j:f(i)](h(x[i], j)))
    Eq << s.this.definition

    Eq << Algebra.EqProd.of.Eq.apply(Eq[-1], (i, 0, k), simplify=False)

    Eq << Eq[-1].this.lhs.expr.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2020-03-03
