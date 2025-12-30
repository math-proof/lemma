from util import *


@apply
def apply(is_real):
    x, C = is_real.of(Element)
    assert C in Reals
    return Element(x ** 2, Interval(0, oo))


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(super_real=True)
    Eq << apply(Element(x, Reals))

    Eq << Set.IsReal.of.IsReal.IsReal.apply(Eq[0], Eq[0])

    Eq << Set.Le.Le.of.In_Icc.apply(Eq[-1])

    Eq << Set.Eq.Square.Abs.of.IsReal.apply(Eq[0])

    Eq <<= Eq[1].subs(Eq[-1].reversed), Eq[2].subs(Eq[-1].reversed)


    Eq <<= Set.In_Ico.given.Le.Lt.apply(Eq[-2]),Set.Le.Le.of.In_Icc.apply(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-06-29
