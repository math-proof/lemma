from util import *


@apply
def apply(ne, self, x=None):
    a = ne.of(Unequal[0])
    from Lemma.Algebra.Le.of.Le.Ge.quadratic import quadratic_coefficient
    x, S[a], b, c = quadratic_coefficient(self, x=x)
    rest = (4 * a * c - b ** 2) / (4 * a)
    rest = rest.ratsimp()
    assert a.is_finite
    return Equal(self, a * (x + b / (2 * a)) ** 2 + rest, evaluate=False)


@prove
def prove(Eq):
    x, a, b, c = Symbol(complex=True)
    Eq << apply(Unequal(a, 0), a * x ** 2 + b * x + c)

    Eq << Eq[1].this.rhs.expand()

    # https://en.wikipedia.org/wiki/Completing_the_square



if __name__ == '__main__':
    run()
# created on 2023-04-30


# updated on 2023-06-30



from . import harmonic_mean
