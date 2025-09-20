from util import *


@apply
def apply(less_than_f, less_than):
    from Lemma.Algebra.Le.of.Eq.Le.subst import ratsimp
    assert less_than_f.is_Greater
    assert less_than.is_Greater

    lhs, rhs, k = ratsimp(less_than_f, less_than)
    assert k > 0
    return Greater(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra
    y, b, x, t = Symbol(real=True)
    k = Symbol(real=True, positive=True)



    Eq << apply(y > x * k + b, x > t)

    Eq << Eq[1] * k + b

    Eq << Algebra.Gt.of.Gt.Gt.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-07-19
