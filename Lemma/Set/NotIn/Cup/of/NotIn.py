from util import *


@apply
def apply(given, limit):
    k, a, b = limit
    e, A = given.of(NotElement)

    assert Range(a, b) in A.domain_defined(k)

    return NotElement(e, Cup[k:a:b](A))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    n = Symbol(positive=True, integer=True, given=False)
    x, k = Symbol(integer=True)

    A = Symbol(shape=(oo,), etype=dtype.integer)

    Eq << apply(NotElement(x, A[k]), (k, 0, n))

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq[0].subs(k, 0)

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << Eq[0].subs(k, n)

    Eq <<= Eq[-1] & Eq[1]

    Eq << Imply(Eq[1], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2020-10-22
