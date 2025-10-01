from util import *


@apply
def apply(given, sgm):
    A, B = given.of(Equal[Intersection, EmptySet])
    fx, (x, s) = sgm.of(Sum)
    S[A], S[B] = s.of(Union)

    return Equal(sgm, Sum[x:A](fx).simplify() + Sum[x:B](fx).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    A, B = Symbol(etype=dtype.integer)
    x = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(Equal(Intersection(A, B), A.etype.emptySet), Sum[x:A | B](f(x)))

    Eq << Algebra.Sum.eq.AddSumS.apply(Eq[1].lhs, cond=B)

    Eq << Set.EqSDiff.of.Inter.eq.Empty.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-02-03
