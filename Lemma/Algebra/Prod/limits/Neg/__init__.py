from util import *


@apply
def apply(self):
    expr, (i,_a, a1) = self.of(Product)
    a = a1 - 1
    assert _a == -a
    return Equal(self, Product[i:-a:a + 1](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Finset

    i = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    f = Function(real=True)
    Eq << apply(Product[i:-n:n + 1](f(i)))

    Eq << Eq[0].subs(n, 0)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Finset.Prod.eq.MulProdS, cond={n + 1})

    Eq << Eq[-1].this.lhs.args[1].apply(Finset.Prod.eq.MulProdS, cond={-n - 1})

    Eq << Eq[-1].this.rhs.apply(Finset.Prod.eq.MulProdS, cond={n + 1})

    Eq << Eq[-1].this.rhs.args[1].apply(Finset.Prod.eq.MulProdS, cond={-n - 1})

    Eq << Eq[0] * f(-n -1) * f(n + 1)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Eq_Ite.of.All_Imp.apply(Eq[-1], n=n, start=0)


if __name__ == '__main__':
    run()
# created on 2020-02-24
from . import Infty
