from util import *


@apply
def apply(given):
    x_in_A, x_in_B = given.of(Imply)

    x, A = x_in_A.of(Element)
    S[x], B = x_in_B.of(Element)
    assert not x.is_given
    assert x.is_symbol

    return Subset(A, B)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.integer[n])

    Eq << apply(Imply(Element(x, A), Element(x, B)))

    Eq << Eq[0].this.apply(Logic.Imp.Is.All, wrt=x)

    Eq << Set.Subset.of.All_In.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-04-25
