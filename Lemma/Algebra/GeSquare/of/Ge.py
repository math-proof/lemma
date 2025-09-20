from util import *



@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual)

    assert lhs.is_real
    assert rhs.is_real
    assert rhs >= 0

    return GreaterEqual(lhs * lhs, rhs * rhs)


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True)
    y = Symbol(real=True, nonnegative=True)

    Eq << apply(GreaterEqual(x, y))

    Eq << Algebra.GeMul.of.Ge.Ge.apply(Eq[0], Eq[0])



if __name__ == '__main__':
    run()

# created on 2019-06-01
