from util import *


@apply
def apply(self):
    expr, (i, a, b) = self.of(Product)

    assert i.is_integer
    back = expr._subs(i, b)
    assert back.is_nonzero
    return Equal(self, Product[i:a:b + 1](expr) / back, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    f, h = Function(real=True, positive=True)

    Eq << apply(Product[i:n](f(i) + h(i)))

    Eq << Eq[-1].this.rhs.find(Product).apply(Finset.Prod.eq.MulProdS, cond={n})


if __name__ == '__main__':
    run()

# created on 2020-03-09
