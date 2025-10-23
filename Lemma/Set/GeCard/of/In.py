from util import *


@apply
def apply(given):
    x, S = given.of(Element)
    return GreaterEqual(Card(S), 1)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat

    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(complex=True, shape=(n,), given=True)
    S = Symbol(etype=dtype.complex[n], given=True)
    Eq << apply(Element(x, S))

    Eq << Set.Ne_Empty.of.In.apply(Eq[0])

    Eq << Set.Gt_0.of.Ne_Empty.apply(Eq[-1])

    Eq << Nat.Ge_Add_1.of.Gt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-10
