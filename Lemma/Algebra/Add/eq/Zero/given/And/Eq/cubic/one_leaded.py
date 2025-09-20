from util import *


def cubic_solve(fx, x, d=None):
    from Lemma.Algebra.And_Imp_Or_EqS.of.Add.eq.Zero.cubic import cubic_coefficient
    S[1], a, b, c = cubic_coefficient(fx, x=x)
    q = a ** 3 / 27 * 2 + c - a * b / 3
    p = b - a ** 2 / 3
    delta = 4 * p ** 3 / 27 + q ** 2
    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    A = (sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    B = (-sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    w = -S.One / 2 + sqrt(3) / 2 * S.ImaginaryUnit
    arg_p = Ceil(3 * Arg(-p / 3) / (S.Pi * 2) - S.One / 2)
    arg_AB = Piecewise((0, Equal(p * Ceil((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True))
    if d is None:
        x0 = A + B
        x1 = A * w + B
        x2 = A * ~w + B
        return arg_p - arg_AB, x0 - a / 3, x1 - a / 3, x2 - a / 3

    if d == 0:
        x0 = A + B
    elif d % 3 == 1:
        x0 = A * w + B
    elif d % 3 == 2:
        x0 = A * ~w + B
    else:
        ...

    return arg_p - arg_AB, x0 - a / 3

@apply
def apply(given, x=None, d=0):
    fx, rhs = given.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs
    _d, x0 = cubic_solve(fx, x, d)

    return Equal(_d, d), Equal(x, x0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a, b, c = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 3 + a * x ** 2 + b * x + c, 0), x=x, d=1)

    x = Symbol(x + a / 3)
    Eq.x_def = x.this.definition

    Eq << Eq.x_def.this.apply(Algebra.Eq.transport, rhs=1).reversed

    Eq << Eq[0].subs(Eq[-1])

    Eq << Eq[-1].this.find(Pow[Add]).apply(Algebra.Pow.eq.Add, simplify=None)

    Eq << Eq[-1].this.find(Pow[Add]).apply(Algebra.Pow.eq.Add, simplify=None)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS, simplify=None)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS, simplify=None)

    Eq << Algebra.Add.eq.Zero.given.And.Eq.cubic.depressed.apply(Eq[-1], x=x, d=1)

    Eq << Eq[-1].subs(Eq.x_def)

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, lhs=1)





if __name__ == '__main__':
    run()
# created on 2018-11-10
# updated on 2023-05-12
