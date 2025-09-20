from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.eq.Add.doit.outer.setlimit import doit
    return Equal(self, doit(Product, self))


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    f = Function(integer=True)

    n = 5
    finiteset = {i for i in range(n)}

    Eq << apply(Product[j:f(i), i:finiteset](x[i, j]))

    s = Symbol(Stack[i](Product[j:f(i)](x[i, j])))

    Eq << s[i].this.definition

    Eq << Algebra.EqProd.of.Eq.apply(Eq[-1], (i, finiteset))

    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.eq.Mul.doit.setlimit)

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition


if __name__ == '__main__':
    run()

# created on 2020-03-07
