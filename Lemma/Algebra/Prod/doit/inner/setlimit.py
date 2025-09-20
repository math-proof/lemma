from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.doit.inner.setlimit import doit
    return Equal(self, doit(Product, self))


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    Eq << apply(Product[j:{0, 1, 2, 3}, i:m](x[i, j]))

    s = Symbol(Stack[i](Product[j:{0, 1, 2, 3}](x[i, j])))

    Eq << s[i].this.definition

    Eq << Algebra.EqProd.of.Eq.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(Algebra.Prod.eq.Mul.doit.setlimit)

    Eq << Eq[-2].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()

# created on 2020-03-03
