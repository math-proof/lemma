from util import *


@apply
def apply(is_complex, eq):
    a, C = is_complex.of(Element)
    assert C in S.Complexes
    b, c = eq.of(Equal)
    return Equal(a + b, a + c)


@prove
def prove(Eq):
    from Lemma import Set

    x, y, z = Symbol(super_complex=True)
    Eq << apply(Element(x, S.Complexes), Equal(y - x, z))

    Eq << Set.Eq.of.In.definition.apply(Eq[0], var='a').reversed

    Eq <<= Eq[1].subs(Eq[-1]), Eq[2].subs(Eq[-1])

    Eq << Eq[-2] + Eq[3].rhs




if __name__ == '__main__':
    run()
# created on 2023-06-06
# updated on 2023-06-29
