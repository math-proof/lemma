from util import *


@apply(simplify=False)
def apply(self, x=None):
    from Lemma.Algebra.Le.of.Le.Ge.quadratic import quadratic_coefficient
    x, a, b, c = quadratic_coefficient(self, x=x)

    assert a.is_finite
    assert a.is_nonzero

    rest = (4 * a * c - b ** 2) /(4 * a)
    rest = rest.ratsimp()
    return Equal(self, a * (x + b / (2 * a)) ** 2 + rest, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a, b, c = Symbol(complex=True, given=True)
    a = Symbol(complex=True, given=True, zero=False)
    Eq << apply(a * x ** 2 + b * x + c)

    Eq << Unequal(a, 0, plausible=True)

    Eq << Algebra.Eq.of.Ne_0.square_completing.apply(Eq[1], Eq[0].lhs, simplify=None)

    # Eq << Eq[0].this.rhs.expand()
    # https://en.wikipedia.org/wiki/Completing_the_square




if __name__ == '__main__':
    run()
# created on 2023-04-10
# updated on 2023-05-03
from . import Conj
