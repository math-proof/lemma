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

    Eq << Eq[0] / c ** (n + 1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Symbol * Pow).args[:2].apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Eq[-1].subs(n, k)

    Eq << Bool.All.of.All_OrNot.apply(Eq[-1], 1)

    Eq << Algebra.EqSumS.of.Eq.apply(Eq[-1], (k, 0, n))

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.subst.offset, -1)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Sub.unshift)

    Eq << Eq[-1] + x[0]

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1] * c ** n

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(Algebra.Mul_Sum.eq.Sum_Mul)





if __name__ == '__main__':
    run()
# created on 2021-09-29
# updated on 2023-06-17
