from util import *


@apply
def apply(given):
    (x, y), S[{0, 1}] = given.of(Equal[FiniteSet])
    return Equal(Matrix([x, y]), Matrix([1 - KroneckerDelta(0, x), KroneckerDelta(0, x)]))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x, y = Symbol(integer=True)
    Eq << apply(Equal({x, y}, {0, 1}))

    Eq << Algebra.Eq.given.And.split.Matrix.apply(Eq[1])



    Eq << Element(x, {x, y}, plausible=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Set.Eq.Delta.Zero.of.In.apply(Eq[-1])

    Eq.x_equality = -Eq[-1] + 1

    Eq << Eq.x_equality.reversed

    Eq << Set.Eq.of.Eq.split.Finset.Add.apply(Eq[0])

    Eq << Eq[-1] + Eq.x_equality

    Eq << Eq[-1].this.apply(Algebra.EqAddS.Is.Eq)

    Eq << Algebra.Eq.of.Sub.eq.Zero.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-04-02
