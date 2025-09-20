from util import *


@apply
def apply(self):
    (x, n), fx = self.of(Equal[Indexed])
    c, (((S[c], k_offset), hk), (k, S[0], S[n])) = fx.of(Expr ** n * x[0] + Sum[Pow * Expr])
    S[-k + n - 1] = k_offset
    assert c.is_nonzero
    return Equal(x[n + 1], x[n] * c + hk._subs(k, n))

@prove
def prove(Eq):
    from Lemma import Algebra

    k, n = Symbol(integer=True)
    c = Symbol(real=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    h = Function(real=True)
    Eq << apply(Equal(x[n], x[0] * c ** n + Sum[k:n](h(k) * c ** (n - k - 1))))

    Eq << Algebra.Eq.of.Eq.rsolve.apply(Eq[1])





if __name__ == '__main__':
    run()
# created on 2021-07-31
# updated on 2023-06-17
