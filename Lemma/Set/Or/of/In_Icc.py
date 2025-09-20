from util import *


@apply(simplify=False)
def apply(given, by, left_open=False):
    e, domain = given.of(Element)
    a, b = domain.of(Interval)

    assert domain.conditionally_contains(by)
    A = domain.copy(stop=by, right_open=not left_open)
    B = domain.copy(start=by, left_open=left_open)
    return Or(Element(e, A), Element(e, B))


@prove
def prove(Eq):
    from Lemma import Set

    x, a, b = Symbol(real=True, given=True, positive=True)
    c = Symbol(domain=Interval(a, b))
    Eq << apply(Element(x, Interval(a, b)), c)

    Eq << Eq[0].this.rhs.apply(Set.Icc.eq.Union, c)

    Eq << Set.OrInS.of.In_Union.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-04-12
# updated on 2023-04-18
