from util import *


@apply
def apply(given, *limits):
    A, fx = given.of(Supset)

    return Supset(A, Cup(fx, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), etype=dtype.complex[n])
    A = Symbol(etype=dtype.complex[n])
    m = Symbol(integer=True, positive=True, given=False)

    Eq << apply(Supset(A, x[i]), (i, 0, m))

    Eq.initial = Eq[-1].subs(m, 1)

    Eq << Eq[0].subs(i, 0)

    Eq.induct = Eq[1].subs(m, m + 1)

    Eq << Eq[0].subs(i, m)

    Eq <<= Eq[-1] & Eq[1]

    Eq << Imply(Eq[1], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n=m, start=1, simplify=None)


if __name__ == '__main__':
    run()

# created on 2021-07-04
