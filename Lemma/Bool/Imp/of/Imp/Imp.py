from util import *



@apply
def apply(is_imply_P, is_imply_Q):
    p, q = is_imply_P.of(Imply)
    _q, r = is_imply_Q.of(Imply)
    if q != _q:
        p, q, S[q], r = _q, r, p, q

    return Imply(p, r)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    p, q, r = Symbol(bool=True)
    Eq << apply(Imply(p, q), Imply(q, r))

    Eq << Eq[0].apply(Bool.Or.of.ImpNot)

    Eq << Eq[1].apply(Bool.Or.of.ImpNot)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-1])

    Eq << Eq[2].apply(Bool.Imp.given.Or_Not)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2018-02-01
# updated on 2022-01-27

