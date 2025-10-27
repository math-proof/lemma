from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    assert domain.left_open
    if domain.right_open:
        assert b.is_infinite
    else:
        if not b.is_integer:
            b = Ceil(b)

    if not a.is_integer:
        a = Floor(a)
    return Element(Ceil(x), Range(a + 1, b + 1))


@prove
def prove(Eq):
    from Lemma import Set

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)))

    Eq << Set.In.of.In.relax.Icc.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Set.Icc.eq.Cup.left_open)

    Eq << Set.Any_In.of.In_Cup.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Set.EqCeil.of.In_Ioc)

    Eq << Eq[-1].this.expr.apply(Set.In.Finset.of.Eq)

    Eq << Set.In.Cup.of.Any_In.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Set.CupIn_Ico.eq.Cup_UnaryFnAdd, -1)




if __name__ == '__main__':
    run()
# created on 2018-10-24
# updated on 2023-04-17
