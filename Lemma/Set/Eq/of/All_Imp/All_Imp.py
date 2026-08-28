from util import *


@apply
def apply(sufficient_A, sufficient_B):
    x_in_A, x_in_B = sufficient_A.of(Imply)

    S[x_in_B], S[x_in_A] = sufficient_B.of(Imply)

    x, A = x_in_A.of(Element)
    S[x], B = x_in_B.of(Element)

    return Equal(A, B)


@prove
def prove(Eq):
    from Lemma import Set, Bool
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.integer[n])

    Eq << apply(Imply(Element(x, A), Element(x, B)), Imply(Element(x, B), Element(x, A)))

    Eq << Eq[0].this.apply(Bool.All_Imp.Is.All, wrt=x)

    Eq << Eq[1].this.apply(Bool.All_Imp.Is.All, wrt=x)

    Eq << Set.Eq.of.All_In.All_In.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-09-20
