from util import *


@apply
def apply(el, self, x=None):
    a, R = el.of(Element)
    assert not R & {0} and R in S.Complexes

    from Lemma.Algebra.Le.of.Le.Ge.quadratic import quadratic_coefficient
    x, S[a], b, c = quadratic_coefficient(self, x=x)
    rest = (4 * a * c - b ** 2) / (4 * a)
    rest = rest.ratsimp()
    return Equal(self, a * (x + b / (2 * a)) ** 2 + rest, evaluate=False)


@prove
def prove(Eq):
    x, a, b, c = Symbol(complex=True)
    Eq << apply(Element(a, S.Complexes - {0}), a * x ** 2 + b * x + c)

    Eq << Eq[1].this.rhs.expand()



if __name__ == '__main__':
    run()
# created on 2023-06-30
