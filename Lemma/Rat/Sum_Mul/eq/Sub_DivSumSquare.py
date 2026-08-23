from util import *


@apply
def apply(self):
    (xi, xj), (j, S[0], i), (S[i], S[0], n) = self.of(Sum[Mul])
    if not xi._has(i):
        xi, xj = xj, xi
    assert xj._subs(j, i) == xi
    return Equal(self, Sum[i:n](xi) ** 2 / 2 - Sum[i:n](xi ** 2) / 2)


@prove
def prove(Eq):
    from Lemma import Algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(Sum[j:i, i:n](x[i] * x[j]))

    Eq << Algebra.Square.Sum.eq.Add.Sum.apply(Eq[0].find(Pow[Sum]))

    Eq << Eq[0].subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2019-11-12
# updated on 2023-06-02
