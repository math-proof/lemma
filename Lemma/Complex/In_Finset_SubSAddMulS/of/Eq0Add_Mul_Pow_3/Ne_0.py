from util import *


def cubic_coefficient(fx, x):
    fx = fx.as_poly(x)
    if fx.degree() != 3:
        return None
    a = fx.nth(3)
    b = fx.nth(2)
    c = fx.nth(1)
    d = fx.nth(0)
    return a, b, c, d

def cubic_root(_a, _b, _c, _d):
    a, b, c = _b / _a, _c / _a, _d / _a
    q = a ** 3 / 27 * 2 + c - a * b / 3
    p = b - a ** 2 / 3
    delta = 4 * p ** 3 / 27 + q ** 2
    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    A = (sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    B = (-sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    arg_p = Ceil(3 * Arg(-p / 3) / (S.Pi * 2) - S.One / 2)
    # arg_AB = Ceil(3 * Arg(A * B) / (S.Pi * 2) - S.One / 2)
    arg_AB = Piecewise((0, Equal(p * Ceil((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True))
    d = arg_p - arg_AB
    return d, A, B, a

@apply
def apply(is_nonzero, given, x=None):
    _a = is_nonzero.of(Unequal[0])
    fx, rhs = given.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs
    if x is None:
        for x in fx.free_symbols:
            p = fx.as_poly(x)
            if p and p.degree() == 3:
                break
        else:
            return

    S[_a], _b, _c, _d = cubic_coefficient(fx, x=x)
    d, A, B, a = cubic_root(_a, _b, _c, _d)
    w = -S.One / 2 + sqrt(3) / 2 * S.ImaginaryUnit
    return Imply(Equal(d, 0), Or(Equal(x, A + B - a / 3), Equal(x, A * w + B * ~w - a / 3), Equal(x, A * ~w + B * w - a / 3))), \
        Imply(Equal(d % 3, 1), Or(Equal(x, A * w + B - a / 3), Equal(x, A * ~w + B * ~w - a / 3), Equal(x, A + B * w - a / 3))), \
        Imply(Equal(d % 3, 2), Or(Equal(x, A * ~w + B - a / 3), Equal(x, A + B * ~w - a / 3), Equal(x, A * w + B * w - a / 3)))


@prove
def prove(Eq):
    from Lemma import Nat, Complex

    x, a, b, c, d = Symbol(complex=True, given=True)
    Eq << apply(Unequal(a, 0), Equal(a * x ** 3 + b * x ** 2 + c * x + d, 0), x=x)

    Eq << Nat.Div.of.Eq.nonzero.apply(Eq[0], Eq[1])

    Eq << Complex.In_Finset_SubSAddMulS.of.Eq0Add_Pow_3.apply(Eq[-1], x=x)


if __name__ == '__main__':
    run()
# created on 2018-11-25
# updated on 2026-08-22
