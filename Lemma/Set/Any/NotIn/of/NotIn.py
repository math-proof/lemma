from util import *


@apply
def apply(given):
    e, s = given.of(NotElement)
    space, *shape = s.of(CartesianSpace)
    k = given.generate_var(integer=True)
    n = e.shape[0]
    return Exists[k:n](NotElement(e[k], CartesianSpace(space, *shape[1:])).simplify())


@prove
def prove(Eq):
    from Lemma import Set

    n, m = Symbol(positive=True, integer=True, given=True)
    x = Symbol(integer=True, shape=(n,), given=True)
    i = Symbol(integer=True)
    Eq << apply(NotElement(Stack[i:n](x[i]), CartesianSpace(Range(0, m), n)))

    Eq << ~Eq[1]

    Eq << Set.In.CartesianSpace.of.All_In.apply(Eq[-1])

    Eq << ~Eq[-1]
    Eq << Eq[0].this.lhs.simplify()




if __name__ == '__main__':
    run()
# created on 2023-07-02
