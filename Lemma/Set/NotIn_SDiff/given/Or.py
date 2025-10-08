from util import *



# given e not in S
@apply
def apply(imply):
    e, S = imply.of(NotElement)
    U, A = S.of(Complement)
    return Or(NotElement(e, U), Element(e, A).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    e = Symbol(integer=True, given=True)
    U, A = Symbol(etype=dtype.integer, given=True)

    Eq << apply(NotElement(e, Complement(U, A)))

    Eq << ~Eq[0]

    Eq <<= Eq[-1] & Eq[1]

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-02-25
