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
    from Lemma import Algebra, Set, Logic

    n, m = Symbol(positive=True, integer=True)
    x = Symbol(integer=True, shape=(n,))
    i = Symbol(integer=True)
    Eq << apply(NotElement(Stack[i:n](x[i]), CartesianSpace(Range(0, m), n)))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.Any.NotIn.of.NotIn)

    Eq << Eq[-1].this.rhs.apply(Set.NotIn.given.Any.NotIn)


if __name__ == '__main__':
    run()
# created on 2023-07-02
