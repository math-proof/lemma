from util import *


@apply
def apply(given):
    (x, y), S[{0, 1}] = given.of(Equal[FiniteSet])
    return Equal(Matrix([x, y]), Matrix([1 - KroneckerDelta(0, x), KroneckerDelta(0, x)]))


@prove
def prove(Eq):
    from Lemma import Set, Int, Nat, Tensor

    x, y = Symbol(integer=True)
    Eq << apply(Equal({x, y}, {0, 1}))

    Eq << Tensor.Eq.Eq.given.Append.apply(Eq[1])



    Eq << Element(x, {x, y}, plausible=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Set.Delta0.eq.Sub1.of.In.apply(Eq[-1])

    Eq.x_equality = -Eq[-1] + 1

    Eq << Eq.x_equality.reversed

    Eq << Set.Add.eq.One.of.Finset.apply(Eq[0])

    Eq << Eq[-1] + Eq.x_equality

    Eq << Eq[-1].this.apply(Nat.Add.Is.Eq)

    Eq << Int.Eq.of.Sub.eq.Zero.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-04-02
