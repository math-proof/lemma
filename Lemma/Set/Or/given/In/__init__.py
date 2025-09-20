from util import *


@apply
def apply(given):
    or_eqs = given.of(Or)

    ss = []
    var = None
    for eq in or_eqs:
        x, s = eq.of(Element)

        if var is None:
            var = x
        else:
            assert x == var
        ss.append(s)

    return Element(x, Union(*ss))


@prove
def prove(Eq):
    from Lemma import Set
    x = Symbol(real=True, given=True)
    A, B, C = Symbol(etype=dtype.real)

    Eq << apply(Or(Element(x, A), Element(x, B), Element(x, C)))

    Eq << Set.OrInS.of.In_Union.apply(Eq[1], simplify=False)


if __name__ == '__main__':
    run()


# created on 2021-02-09
from . import Finset
