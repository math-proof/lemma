from util import *


@apply
def apply(eq_p0, eq_p, c):
    p = eq_p0.of(Equal[Indexed[0], 1])
    (S[p], k), ((p, k2floork), (x, k2floor)) = eq_p.of(Equal[Indexed, Indexed * Indexed])

    S[k], S[2 ** k2floor] = k2floork.of(Expr - Expr)
    S[k], S[2] = k2floor.of(Floor[Log / Log])
    n = x.shape[0]
    i = Symbol(integer=True)
    assert p.shape[0] == c.shape[0]
    return Equal(p @ c, Sum[k:2 ** n](Product[i:n](x[i] ** Bool(Equal((k // 2 ** i) % 2, 1))) * c[k]))



@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(n,))
    c, p = Symbol(shape=(2 ** n,))
    k = Symbol(integer=True)
    Eq << apply(Equal(p[0], 1), Equal(p[k], x[Floor(log(k) / log(2))] * p[k - 2 ** (Floor(log(k) / log(2)))]), c)

    


if __name__ == '__main__':
    run()
# created on 2021-12-23
# updated on 2022-01-04