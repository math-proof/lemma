from util import *


@apply
def apply(self, sgm):
    ((xi, lt), (xi_1, _true)), yi = self.of(Equal[Piecewise])
    i, t = lt.of(Less)
    assert xi._subs(i, i + 1) == xi_1

    fyi, (S[i], *ab) = sgm.of(Sum)
    if ab:
        S[0], n = ab
    else:
        domain = fyi.domain_defined(i)
        S[0], n = domain.of(Range)
    n += 1

    assert 0 <= t < n
    assert fyi._has(yi)

    fxi = fyi._subs(yi, xi)
    return Equal(sgm, Sum[i:n](fxi) - fxi._subs(i, t))


@prove
def prove(Eq):
    i = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo))
    x, y = Symbol(real=True, shape=(oo,))
    t = Symbol(domain=Range(n))
    f = Function(real=True)
    Eq << apply(Equal(y[i], Piecewise((x[i], i < t),(x[i + 1], True))), Sum[i:n - 1](f(y[i])))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-11-27
