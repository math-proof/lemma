from util import *


@apply(simplify=False)
def apply(given):
    x, s = given.of(NotElement)

    return Element(x, x.domain - s)


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(NotElement(x, S))

    Eq << Set.In.NotIn.of.In_SDiff.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2023-05-21
