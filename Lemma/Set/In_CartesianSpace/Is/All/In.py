from util import *


@apply
def apply(given):
    e, s = given.of(Element)
    space, *shape = s.of(CartesianSpace)
    k = given.generate_var(integer=True)
    n = e.shape[0]
    return ForAll[k:n](Element(e[k], CartesianSpace(space, *shape[1:])).simplify())


@prove(provable=False)
def prove(Eq):
    n, m = Symbol(positive=True, integer=True)
    x = Symbol(integer=True, shape=(n,))
    i = Symbol(integer=True)
    Eq << apply(Element(Stack[i:n](x[i]), CartesianSpace(Range(0, m), n)))


if __name__ == '__main__':
    run()
# created on 2023-07-02
