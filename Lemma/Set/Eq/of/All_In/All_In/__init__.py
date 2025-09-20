from util import *


@apply
def apply(all_A, all_B):
    (x, B), (S[x], A) = all_A.of(All[Element])
    (S[x], S[A]), (S[x], S[B]) = all_B.of(All[Element])

    return Equal(A, B)


@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.integer[n])

    Eq << apply(All[x:A](Element(x, B)), All[x:B](Element(x, A)))

    Eq << Set.Subset.of.All_In.apply(Eq[0])

    Eq << Set.Subset.of.All_In.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2018-04-27

from . import All_Eq
