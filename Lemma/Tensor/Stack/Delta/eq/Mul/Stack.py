from util import *


@apply
def apply(self):
    ((i, _j), expr), (j, S[0], n) = self.of(Stack[Mul[KroneckerDelta]])

    if not _j._has(j):
        i, _j = _j, i

    dif = _j - j
    assert not i._has(j)
    assert not dif._has(j)
    assert expr._has(j)

    expr = expr._subs(j, i - dif)

    return Equal(self, expr * Stack[j:n](KroneckerDelta(i, _j)))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(real=True, shape=(oo,))
    Eq << apply(Stack[j:n](a[j] * KroneckerDelta(i, j + 1)))

    t = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], t)





if __name__ == '__main__':
    run()
# created on 2021-12-30
# updated on 2022-01-04
