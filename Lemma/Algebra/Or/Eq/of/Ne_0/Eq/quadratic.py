from util import *


@apply
def apply(is_nonzero, eq, x=None):
    from Lemma.Algebra.Le.of.Le.Ge.quadratic import quadratic_coefficient
    a = is_nonzero.of(Unequal[0])
    fx, rhs = eq.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs

    x, S[a], b, c = quadratic_coefficient(fx, x=x)
    delta = b * b - 4 * a * c

    return Or(Equal(x, (-b + sqrt(delta)) / (a * 2)), Equal(x, (-b - sqrt(delta)) / (a * 2)))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a, b, c = Symbol(complex=True, given=True)
    Eq << apply(Unequal(a, 0), Equal(a * x ** 2 + b * x + c, 0), x=x)

    x = Symbol(x + b / (2 * a))
    Eq << x.this.definition

    Eq << Eq[-1] - b / (2 * a)

    Eq << Eq[-1].reversed

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Algebra.Or.Eq.Square.of.Ne_0.Eq.apply(Eq[0], Eq[-1].reversed, x=x)

    Eq << Eq[-1].subs(x.this.definition)

    Eq << Eq[-1].this.args[1] - b / (2 * a)

    Eq << Eq[-1].this.args[1] - b / (2 * a)

    Eq << Eq[2].this.args[0].rhs.expand()

    Eq << Eq[-1].this.args[0].rhs.expand()





if __name__ == '__main__':
    run()
# created on 2018-08-15
# updated on 2023-05-20
