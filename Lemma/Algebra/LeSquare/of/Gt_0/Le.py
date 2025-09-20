from util import *


@apply
def apply(is_positive, le):
    x = is_positive.of(Expr > 0)
    S[x], M = le.of(LessEqual)

    return LessEqual(x * x, M * M)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, M = Symbol(real=True)
    Eq << apply(x > 0, x <= M)

    Eq << Algebra.Ge.of.Gt.relax.apply(Eq[0])

    Eq << Algebra.LeSquare.of.Ge_0.Le.apply(Eq[-1], Eq[1])










if __name__ == '__main__':
    run()
# created on 2019-08-22
