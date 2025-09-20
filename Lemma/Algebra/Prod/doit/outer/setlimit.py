from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.doit.outer.setlimit import doit
    return Equal(self, doit(Product, self))


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j, k, a = Symbol(integer=True)
    f, g = Function(etype=dtype.integer)


    Eq << apply(Product[k:g(i), j:f(i), i:{a}](x[i, j]))

    @Function(real=True)
    def s(i):
        return Product[k:g(i), j:f(i)](x[i, j])

    Eq << s(i).this.defun()

    Eq << Algebra.EqProd.of.Eq.apply(Eq[-1], (i, {a}))

    Eq << Eq[-1].this.lhs.defun()

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2020-03-05
