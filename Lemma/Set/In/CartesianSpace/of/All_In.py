from util import *


@apply(simplify=False)
def apply(given):
    (e, s), *limits = given.of(All[Element])

    shape = []
    for limit in limits:
        x, S[0], b = limit
        assert x.is_integer
        assert e._has(x)
        shape.append(b)
    shape.reverse()
    return Element(Stack(e, *limits).simplify(), CartesianSpace(s, *shape))


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(integer=True, shape=(oo,))
    S = Symbol(etype=dtype.integer)
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(All[i:n](Element(x[i], S)))

    Eq << Set.In_CartesianSpace.given.All.In.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2022-09-20
# updated on 2023-07-02
