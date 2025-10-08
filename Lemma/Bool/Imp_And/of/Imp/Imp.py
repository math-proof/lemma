from util import *



@apply
def apply(is_imply_P, is_imply_Q):
    p, x = is_imply_P.of(Imply)
    q, y = is_imply_Q.of(Imply)

    return Imply(p & q, x & y)


@prove
def prove(Eq):
    from Lemma import Bool
    x, y, a, b = Symbol(real=True, given=True)

    Eq << apply(Imply(x > 0, a > 0), Imply(y > 0, b > 0))

    Eq << Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Bool.Cond.of.And, index=0)

    Eq << Eq[-1].this.lhs.apply(Bool.Cond.of.And, index=1)


if __name__ == '__main__':
    run()
# created on 2018-03-28
