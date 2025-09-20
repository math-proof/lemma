from util import *


@apply
def apply(is_negative, self, div=False):
    factor = is_negative.of(Expr < 0)
    args = self.of(Min)

    if div:
        args = [arg * factor for arg in args]
        rhs = Max(*args) / factor
    else:
        args = [arg / factor for arg in args]
        rhs = Max(*args) * factor

    return Equal(self, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    r = Symbol(real=True)
    Eq << apply(r < 0, Min(r * x, r * y))

    Eq << Algebra.Div.lt.Zero.of.Lt_0.apply(Eq[0])

    Eq << Algebra.Max.eq.Mul.Min.of.Lt_0.apply(Eq[-1], Eq[1].find(Max))

    Eq << Eq[-1] * r

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2021-10-02
