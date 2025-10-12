from util import *


@apply
def apply(is_positive, lt):
    x = is_positive.of(Expr > 0)
    S[x], M = lt.of(Less)

    return Less(x * x, M * M)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, M = Symbol(real=True)
    Eq << apply(x > 0, x < M)

    Eq << Nat.Ge.of.Gt.apply(Eq[0])

    Eq << Algebra.LtSquare.of.Ge_0.Lt.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-08-28
