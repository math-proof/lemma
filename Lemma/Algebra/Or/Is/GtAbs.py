from util import *


@apply
def apply(ou):
    (x, a), (S[x], S[-a]) = ou.of((Expr < Expr) | (Expr > Expr))
    return abs(x) > -a


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(Or(x < -a, x > a))

    Eq << Eq[0].this.rhs.apply(Algebra.GtAbs.Is.Or)


if __name__ == '__main__':
    run()
# created on 2023-04-18
