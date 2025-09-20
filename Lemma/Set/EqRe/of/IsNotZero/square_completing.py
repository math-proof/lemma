from util import *


def extract(expr, z):
    expr, a = expr.of_simple_poly(abs(z) ** 2)
    if a:
        if expr.is_Add:
            (expr, coeff), c = expr.of(Re * Expr + Expr)
        else:
            c = 0
            expr, coeff = expr.of(Re * Expr)

        coeff /= 2
        if expr._has(~z):
            b = expr / ~z
            b = ~b

        elif expr._has(z):
            b = expr / z

        else:
            return

        assert not b._has(z)
        return a, coeff * b, c

def quadratic_coefficient(self, z=None):
    if z is None:
        for z in self.free_symbols:
            z_bar = ~z
            if z_bar == z:
                continue

            if coeffs := extract(self, z):
                return z, *coeffs
        else:
            return
    else:
        coeffs = extract(self, z)
        return z, *coeffs

@apply
def apply(el, self, z=None):
    a, R = el.of(Element)
    assert not R & {0} and R in Reals
    # coeffs[i, j] is the coefficient of z ** i * (~z) ** j
    z, S[a], b, c = quadratic_coefficient(self, z)

    rest = c - abs(b) ** 2 / a
    z += ~b / a
    return Equal(self, a * abs(z) ** 2 + rest, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    z, a, b, c = Symbol(complex=True)
    Eq << apply(Element(a, Reals - {0}), a * abs(z) ** 2 + 2 * Re(b * z) + c)

    Eq << Eq[1].this.find(Abs ** 2).apply(Algebra.Square.Abs.eq.Mul.Conj)

    Eq << Eq[-1].this.find(Re).apply(Algebra.Re.eq.Add.Conj)

    Eq << Eq[-1].this.find(Abs ** 2).apply(Algebra.Square.Abs.eq.Mul.Conj)

    Eq << Eq[-1].this.find(Abs ** 2).apply(Algebra.Square.Abs.eq.Mul.Conj)

    Eq << Set.EqConj.of.IsNotZero.square_completing.apply(Eq[0], Eq[-1].lhs)


if __name__ == '__main__':
    run()
# created on 2023-06-25
