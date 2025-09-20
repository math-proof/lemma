from util import *


@apply
def apply(eq, lt):
    from Lemma.Algebra.Le.of.Eq.Le.subst import ratsimp
    assert eq.is_Equal
    assert lt.is_Less

    lhs, rhs, k = ratsimp(eq, lt)
    assert k < 0
    return Greater(lhs, rhs)


@prove
def prove(Eq):
    y, b, x, t = Symbol(real=True)
    k = Symbol(real=True, negative=True)

    Eq << apply(Equal(y, x * k + b), x < t)

    Eq << Eq[1] * k + b

    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
# created on 2021-09-10
