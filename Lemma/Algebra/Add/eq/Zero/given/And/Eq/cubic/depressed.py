from util import *


@apply
def apply(is_zero, x=None, d=0):
    from Lemma.Algebra.And_Imp_Or_EqS.of.Add.eq.Zero.cubic import cubic_coefficient
    fx = is_zero.of(Equal[0])
    S[1], S[0], p, q = cubic_coefficient(fx, x=x)

    delta = 4 * p ** 3 / 27 + q ** 2
    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    A = (sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    B = (-sqrt(delta) / 2 - q / 2) ** (S.One / 3)

    w = -S.One / 2 + S.ImaginaryUnit * sqrt(3) / 2
    arg_p = Ceil(3 * Arg(-p / 3) / (S.Pi * 2) - S.One / 2)
    arg_AB = Piecewise((0, Equal(p * Ceil((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True))

    if d == 0:
        x0 = A + B
    elif d % 3 == 1:
        x0 = A * w + B
    elif d % 3 == 2:
        x0 = A * ~w + B
    else:
        ...

    return Equal(arg_p - arg_AB, d), Equal(x, x0)



@prove
def prove(Eq):
    from Lemma import Algebra, Trigonometry

    x, p, q = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 3 + p * x + q, 0), x=x, d=1)

    Eq.w, Eq.w_conj, Eq.add_ww, Eq.mul_ww, Eq.w_square, Eq.w_conj_square, Eq.w3 = Algebra.AndEqS.omega.apply('omega')

    B, A = Eq[2].rhs.args
    A = Symbol(A)
    B = Symbol(B.find(Pow))
    Eq.A, Eq.B = A.this.definition, B.this.definition

    Eq << Eq[2].subs(Eq.A.reversed, Eq.B.reversed, Eq.w.reversed)

    Eq << Eq[0].subs(Eq[-1])

    Eq << Eq[-1].this.find(Pow).apply(Algebra.Pow.eq.Add)

    Eq << Eq[-1].subs(Eq.w3, Eq.w_square)

    Eq <<= Algebra.EqPowS.of.Eq.apply(Eq.A, exp=3), Algebra.EqPowS.of.Eq.apply(Eq.B, exp=3)

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-4].subs(Eq[-1])

    w = Eq.w.lhs
    Eq << Eq[-1].this.lhs.apply(Algebra.Add.collect, factor=A * B) * w

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.lhs.args[0].apply(Algebra.Mul.distribute, 0)

    Eq << Eq[-1].subs(Eq.w_square)

    Eq.eq = Eq[-1].this.lhs.apply(Algebra.Add.collect, factor=A * w + B * ~w)

    Eq << Eq.A * Eq.B

    Eq << Algebra.EqPowS.of.Eq.apply(Eq[-1], exp=3)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Algebra.Eq.of.Eq_Pow.cubic_root.omega.apply(Eq[-1]) * 3

    Eq << Eq[-1].this.rhs.subs(Eq.A, Eq.B)

    Eq << Eq[-1].this.find(Ceil).apply(Algebra.Ceil.Arg.eq.Ite)

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].this.find(Exp).apply(Trigonometry.ExpMulI.eq.AddCos_MulISin.Euler)

    Eq << Eq[-1].subs(Eq.w_conj.reversed)

    Eq << Eq.eq.subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.mul_ww)


if __name__ == '__main__':
    run()
# created on 2018-11-10
# updated on 2023-04-05
