from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.eq.Add.doit.setlimit import doit
    return Equal(self, doit(Product, self))


@prove
def prove(Eq):
    from Lemma import Algebra
    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo, k))
    i = Symbol(integer=True)

    n = 5
    finiteset = {i for i in range(n)}

    Eq << apply(Product[i:finiteset](x[i]))

    n -= 1
    Eq << Eq[-1].this.lhs.apply(Algebra.Prod.eq.MulProdS, cond={n}, simplify=False)

    Eq << Eq[-1].this.lhs.find(Product).simplify()

    n -= 1
    Eq << Eq[-1].lhs.find(Product).this.apply(Algebra.Prod.eq.MulProdS, cond={n}, simplify=False)

    Eq << Eq[-1].this.rhs.find(Product).simplify()

    n -= 1
    Eq << Eq[-1].rhs.find(Product).this.apply(Algebra.Prod.eq.MulProdS, cond={n})

    Eq << Eq[-1].this.rhs.find(Product).simplify()

    n -= 1
    Eq << Eq[-1].rhs.find(Product).this.apply(Algebra.Prod.eq.MulProdS, cond={n})

    Eq << Eq[5].subs(Eq[-1])

    Eq << Eq[4].subs(Eq[-1])

    Eq << Eq[2].subs(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-03-02
