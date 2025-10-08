from util import *


@apply
def apply(self, k=None):
    (x, n), fx = self.of(Equal[Indexed])
    if n.is_Add:
        offset, n = n.of(Add)
    else:
        offset = 0

    c, item = fx.of(Expr * x[n + offset - 1] + Expr)
    if k is None:
        k = self.generate_var(integer=True)

    assert c.is_nonzero
    return Equal(x[n], x[0] * c ** n + Sum[k:n](item._subs(n, k) * c ** (n - k - 1)))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True)
    c = Symbol(real=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    h = Function(real=True)
    Eq << apply(Equal(x[n + 1], x[n] * c + h(n)), k)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.rhs.apply(Algebra.Eq_Sum.given.Eq.rsolve)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.given.Eq.rsolve, k)





if __name__ == '__main__':
    run()
# created on 2020-10-07
# updated on 2023-06-17
