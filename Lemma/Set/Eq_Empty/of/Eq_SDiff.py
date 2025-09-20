from util import *


@apply
def apply(given):
    (A, B), S[A] = given.of(Equal[Complement])

    return Equal(A & B, A.etype.emptySet)


@prove
def prove(Eq):
    from Lemma import Set
    A, B = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Equal(A - B, A))

    Eq << Eq[0].apply(Set.EqInter.of.Eq, B).reversed


if __name__ == '__main__':
    run()

# created on 2021-04-04
