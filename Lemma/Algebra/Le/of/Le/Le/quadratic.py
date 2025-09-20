from util import *



@apply
def apply(x_less_than_1, y_less_than_1):
    x, S[1] = x_less_than_1.of(LessEqual)
    y, S[1] = y_less_than_1.of(LessEqual)

    assert x >= 0
    assert y >= 0
    return LessEqual(x * x + y * y - 1, x * y)




@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, nonnegative=True)
    Eq << apply(x <= 1, y <= 1)

    Eq.is_nonpositive = Eq[-1] - Eq[-1].rhs

    Eq << GreaterEqual(x, 0, plausible=True)

    Eq.le = Algebra.Le.of.Le.Ge.quadratic.apply(Eq[-1], Eq[0], quadratic=Eq.is_nonpositive.lhs)

    Eq << GreaterEqual(y, 0, plausible=True)

    Eq << Algebra.Le.of.Le.Ge.quadratic.apply(Eq[-1], Eq[1], quadratic=Eq.le.rhs.args[0])

    Eq << Algebra.Le.of.Le.Ge.quadratic.apply(Eq[-2], Eq[1], quadratic=Eq.le.rhs.args[1])

    Eq << Algebra.LeMax.of.Le.Le.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Le.of.Le.Le.apply(Eq[-1], Eq.le)


if __name__ == '__main__':
    run()
# created on 2019-11-22
