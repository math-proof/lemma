from util import *


@apply
def apply(self):
    (x, n), (S[n], S[oo]) = self.of(Limit[Pow])
    assert -1 < x < 1
    return Equal(self, Zeros(*x.shape))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus

    n = Symbol(integer=True)
    x = Symbol(domain=Interval(-1, 1, left_open=True, right_open=True))
    Eq << apply(Limit[n:oo](x ** n))

    Eq << Less(Abs(x), 1, plausible=True)

    Eq << Algebra.LtAbs.given.And.apply(Eq[-1])

    Eq << Calculus.Eq_0.Limit.of.LtAbs.geometric_series.apply(Eq[1], n)




if __name__ == '__main__':
    run()
# created on 2023-04-15
