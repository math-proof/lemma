from util import *


@apply
def apply(given, index=0):
    B, A = given.of(Subset)
    e = B.of(FiniteSet)
    if isinstance(e, tuple):
        e = e[index]

    return Element(e, A)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    n = Symbol(complex=True, positive=True)
    A = Symbol(etype=dtype.complex[n])
    x, y = Symbol(complex=True, shape=(n,))
    Eq << apply(Subset({x, y}, A))

    Eq << Set.All_In.of.Subset.apply(Eq[0])
    Eq << Algebra.Cond.of.All.subst.apply(Eq[-1], Eq[-1].variable, x)


if __name__ == '__main__':
    run()


# created on 2020-07-27


