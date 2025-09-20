from util import *


@apply
def apply(given, *limits):
    e, s = given.of(Element)

    shape = []
    for limit in limits:
        x, S[0], b = limit
        assert x.is_integer
        assert e._has(x)
        shape.append(b)
    shape.reverse()
    return Element(Stack(e, *limits).simplify(), CartesianSpace(s, *shape), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    x = Symbol(integer=True, shape=(oo,))
    S = Symbol(etype=dtype.integer)
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Element(x[i], S), (i, 0, n))

    Eq << Set.In_CartesianSpace.given.All.In.apply(Eq[1])


    Eq << Logic.AllIn.of.All.apply(Eq[0], (i, 0, n))





if __name__ == '__main__':
    run()

# created on 2021-03-03
# updated on 2023-07-02
