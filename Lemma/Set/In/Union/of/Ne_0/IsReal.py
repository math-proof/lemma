from util import *


@apply
def apply(ne_zero, is_real):
    x = ne_zero.of(Unequal[0])
    S[x], R = is_real.of(Element)
    assert R in Reals
    return Element(x, Reals - {0})


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(complex=True)
    Eq << apply(Unequal(x, 0), Element(x, Reals))

    Eq << Set.In_SDiff.of.In.Ne.apply(Eq[0], Eq[1])




if __name__ == '__main__':
    run()
# created on 2023-05-02
