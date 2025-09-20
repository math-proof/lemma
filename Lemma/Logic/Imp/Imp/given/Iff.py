from util import *


@apply
def apply(is_imply_P, is_imply_Q):
    p, q = is_imply_P.of(Imply)
    S[q], S[p] = is_imply_Q.of(Imply)
    return Iff(p, q)


@prove
def prove(Eq):
    p, q = Symbol(bool=True)
    Eq << apply(Imply(p, q), Imply(q, p))
    
    Eq <<= Eq[0] & Eq[1]


if __name__ == '__main__':
    run()
# created on 2022-01-27
