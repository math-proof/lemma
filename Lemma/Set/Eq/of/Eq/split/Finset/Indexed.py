from util import *


# given : A & B = A | B => A = B


@apply
def apply(given):
    (x, y), ((a, S[0]), (S[a], S[1])) = given.of(Equal[FiniteSet, FiniteSet[Indexed, Indexed]])
    return Equal(Matrix([x, y]), Matrix([a[1 - KroneckerDelta(a[0], x)], a[KroneckerDelta(a[0], x)]]))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    x, y = Symbol(etype=dtype.complex, given=True)
    a = Symbol(etype=dtype.complex, shape=(oo,), given=True)
    Eq << apply(Equal({x, y}, {a[0], a[1]}))

    Eq << Algebra.Eq.given.And.split.Matrix.apply(Eq[1])

    Eq << Element(x, {x, y}, plausible=True)

    Eq.x_contains = Eq[-1].subs(Eq[0])

    Eq << Set.OrEqS.of.In_Finset.apply(Eq.x_contains, simplify=False)

    Eq << Eq[2].apply(Logic.Cond.given.Or.OrNot, cond=Equal(x, a[0]))

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].this.apply(Algebra.Cond.of.Ne.Cond.subst, ret=0), Eq[-1].this.apply(Algebra.Cond.Delta.of.Eq.Cond, ret=0)

    Eq << Eq[-1].apply(Set.NotIn.of.Ne.Ne, simplify=False)

    Eq <<= Eq.x_contains & Eq[-1]

    Eq << Eq[3].apply(Logic.Cond.given.Or.OrNot, cond=Equal(x, a[0]))

    Eq << Logic.And_And.given.And.Cond.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq.a00, Eq.a01 = Eq[-2].this.apply(Algebra.Cond.of.Ne.Cond.subst, ret=0), Eq[-1].this.apply(Algebra.Cond.Delta.of.Eq.Cond, ret=0)

    Eq << Eq.a00.apply(Set.NotIn.of.Ne.Ne, simplify=False)

    Eq << Element(a[0], {a[0], a[1]}, plausible=True)

    Eq << Eq[-1].subs(Eq[0].reversed)

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Element(y, {x, y}, plausible=True)

    Eq.y_contains = Eq[-1].subs(Eq[0])

    Eq << Set.OrEqS.of.In_Finset.apply(Eq.y_contains, simplify=False)

    Eq <<= Eq[-1] & Eq.a01

    Eq << Element(a[1], {a[0], a[1]}, plausible=True)

    Eq << Eq[-1].subs(Eq[0].reversed)

    Eq << Set.OrEqS.of.In_Finset.apply(Eq[-1], simplify=False)

    Eq <<= Eq[-1] & Eq[-4]

    Eq <<= Imply(And(*Eq[-1].args[::2]), And(*Eq[-1].args[::2]), plausible=True), Imply(And(*Eq[-1].args[1::2]), And(*Eq[-1].args[1::2]), plausible=True)

    Eq <<= Eq[-2].this.rhs.apply(Logic.Eq.of.Eq.Eq), Eq[-1].this.rhs.apply(Algebra.Ne.of.Eq.Ne)

    Eq << Logic.ImpAndS.of.Imp.Imp.apply(Eq[-2], Eq[-1])

    Eq << ~Eq[-1]




if __name__ == '__main__':
    run()

# created on 2021-04-02
# updated on 2023-05-17
