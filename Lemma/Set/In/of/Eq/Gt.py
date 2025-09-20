from util import *


@apply
def apply(equality, is_positive):
    (e_set, s), a = equality.of(Equal[Intersection])

    if not e_set.is_FiniteSet:
        s, e_set = e_set, s

    e = e_set.of(FiniteSet)

    x_abs = is_positive.is_positive_relationship()
    assert x_abs is not None
    assert a == x_abs.of(Card)

    return Element(e, s)


@prove
def prove(Eq):
    from Lemma import Set
    s, A = Symbol(etype=dtype.integer)
    e = Symbol(integer=True)

    Eq << apply(Equal(e.set & s, A), Greater(Card(A), 0))

    Eq << Set.Ne_Empty.of.Gt_0.apply(Eq[1])

    Eq << Eq[-1].subs(Eq[0].reversed)

    Eq << Set.In.of.Ne_Empty.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-04-01
