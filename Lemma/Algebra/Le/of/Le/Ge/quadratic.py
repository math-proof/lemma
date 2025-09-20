from util import *


def quadratic_coefficient(fx, x=None):
    if x is None:
        for x in fx.free_symbols:
            p = fx.as_poly(x)
            if p is None:
                continue
            if p.degree() == 2:
                break
        else:
            return
    else:
        p = fx.as_poly(x)
        if p.degree() != 2:
            return

    b = p.coeff_monomial(x)
    a = p.coeff_monomial(x * x)
    c = p.coeff_monomial(1)
    return x, a, b, c


@apply
def apply(greater_than, less_than, quadratic=None):
    x, m = greater_than.of(GreaterEqual)
    S[x], M = less_than.of(LessEqual)
    x, a, b, c = quadratic_coefficient(quadratic, x)

    assert a > 0
    return LessEqual(quadratic, Max(a * m * m + b * m + c, a * M * M + b * M + c))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, m, M, b, c = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(x >= m, x <= M, quadratic=a * x * x + b * x + c)

    x = Symbol(x + b / (2 * a))
    Eq.x_definition = x.this.definition

    Eq << Eq.x_definition - Eq.x_definition.rhs.args[1]

    Eq.x_original_definition = Eq[-1].reversed

    Eq << Eq[0].subs(Eq.x_original_definition)

    Eq << Eq[-1] + b / (2 * a)

    Eq << Eq[1].subs(Eq.x_original_definition)

    Eq << Eq[-1] + b / (2 * a)

    Eq << Algebra.LeSquare.of.Le.Ge.apply(Eq[-3], Eq[-1])

    Eq << Eq[-1].subs(Eq.x_definition)

    Eq << Eq[-1] * a

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1] - b * b / (4 * a) + c

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Max)


if __name__ == '__main__':
    run()
# created on 2019-10-26
