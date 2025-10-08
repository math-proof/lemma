from util import *



@apply
def apply(x_imply_P, y_imply_P):
    x, p = x_imply_P.of(Imply)
    y, q = y_imply_P.of(Imply)

    return Imply(x | y, p | q)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    p0, p1, q0, q1 = Symbol(bool=True)
    Eq << apply(Imply(p0, q0), Imply(p1, q1))

    Eq << Eq[-1].apply(Bool.Imp.given.Or_Not)

    Eq << ~Eq[-1]

    Eq << Eq[0].apply(Bool.Or.of.ImpNot)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-1])

    Eq << Eq[1].apply(Bool.Or.of.ImpNot)

    Eq <<= Eq[-2] & Eq[-1]




if __name__ == '__main__':
    run()
# created on 2018-02-09
# updated on 2022-01-27
