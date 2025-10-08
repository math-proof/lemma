from util import *


@apply
def apply(given, n=None, a=0):
    a = sympify(a)
    Zn1, rhs = given.of(Equal)
    r, Zn = rhs.of(Mul)
    if Zn._subs(n, n + 1) != Zn1:
        r, Zn = Zn, r

    assert Zn._subs(n, n + 1) == Zn1
    Za = Zn._subs(n, a)
    if n is None:
        n, *_ = Zn.free_symbols - r.free_symbols

    return Equal(Zn, Za * r ** (n - a))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    n = Symbol(integer=True, nonnegative=True, given=False)
    r = Symbol(complex=True)
    f = Symbol(shape=(oo,), complex=True)

    Eq << apply(Equal(f[n + 1], r * f[n]), n=n)

    Eq << Eq[1].subs(n, 0)

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << Eq[1] * r

    Eq << Eq[-1].this.rhs.powsimp()

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[0], Eq[-1])

    Eq << Imply(Eq[1], Eq.induct, plausible=True)

    Eq << Bool.Eq_Ite.of.All_Imp.apply(Eq[-1], n=n)


if __name__ == '__main__':
    run()

# created on 2019-04-05
