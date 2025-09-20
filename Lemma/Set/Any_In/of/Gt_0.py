from util import *


@apply
def apply(given):
    abs_S, size = given.of(Greater)
    assert size.is_extended_nonnegative
    S = abs_S.of(Card)
    x = S.element_symbol()
    return Any[x](Element(x, S))


@prove
def prove(Eq):
    from Lemma import Set
    A = Symbol(etype=dtype.integer)
    Eq << apply(Card(A) > 0)

    Eq << Set.Ne_Empty.of.Gt_0.apply(Eq[0])

    Eq << Set.Any_In.of.Ne_Empty.apply(Eq[-1], simplify=False)


if __name__ == '__main__':
    run()

# created on 2020-07-13
