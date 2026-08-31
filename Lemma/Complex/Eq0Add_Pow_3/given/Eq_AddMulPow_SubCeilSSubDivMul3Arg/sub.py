from util import *


@apply
def apply(is_zero, x=None, d=0):
    from Lemma.Complex.In_Finset_SubSAddMulS.of.Eq0Add_Mul_Pow_3.Ne_0 import cubic_coefficient
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
    from Lemma import Nat, Real, Int, Complex, Finset

    x, p, q = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 3 + p * x + q, 0), x=x, d=1)

    w = Symbol('omega', -S.One / 2 + S.ImaginaryUnit * sqrt(3) / 2)
    Eq.w = w.this.definition
    Eq.w_conj = Complex.Conj.of.Eq.apply(Eq.w)
    Eq.mul_ww = (Eq.w_conj * Eq.w).this.rhs.apply(Nat.Mul_Add.eq.AddMulS, deep=True)
    Eq.w_square = (Eq.w ** 2).this.rhs.apply(Nat.SquareAdd.eq.AddAdd_SquareS_Mul2Add)
    Eq.w_square = Eq.w_square.subs(Eq.w_conj.reversed)
    Eq.w3 = (Eq.w_square * Eq.w.lhs).subs(Eq.mul_ww)

    B, A = Eq[2].rhs.args
    A = Symbol(A)
    B = Symbol(B.find(Pow))
    Eq.A, Eq.B = A.this.definition, B.this.definition

    Eq << Eq[2].subs(Eq.A.reversed, Eq.B.reversed, Eq.w.reversed)

    Eq << Eq[0].subs(Eq[-1])

    Eq << Eq[-1].this.find(Pow).apply(Finset.PowAdd.eq.Sum_MulMulPowS)

    Eq << Eq[-1].subs(Eq.w3, Eq.w_square)

    Eq <<= Nat.Pow.of.Eq.apply(Eq.A, exp=3), Nat.Pow.of.Eq.apply(Eq.B, exp=3)

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-4].subs(Eq[-1])

    w = Eq.w.lhs
    Eq << Eq[-1].this.lhs.apply(Int.AddAddS.eq.MulAddS, factor=A * B) * w

    Eq << Eq[-1].this.lhs.apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.lhs.args[0].apply(Nat.Mul.distribute, 0)

    Eq << Eq[-1].subs(Eq.w_square)

    Eq.eq = Eq[-1].this.lhs.apply(Int.AddAddS.eq.MulAddS, factor=A * w + B * ~w)

    Eq << Eq.A * Eq.B

    Eq << Nat.Pow.of.Eq.apply(Eq[-1], exp=3)

    Eq << Eq[-1].this.rhs.apply(Nat.Mul_Add.eq.AddMulS, deep=True)

    Eq << Complex.Eq_Mul_Pow_SubCeilS.of.Pow_3.apply(Eq[-1]) * 3

    Eq << Eq[-1].this.rhs.subs(Eq.A, Eq.B)

    Eq << Eq[-1].this.find(Ceil).apply(Complex.CeilSubDivMul3Arg.eq.IteEqMul_Ceil_0)

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].this.find(Exp).apply(Real.ExpMulI.eq.AddCos_MulISin)

    Eq << Eq[-1].subs(Eq.w_conj.reversed)

    Eq << Eq.eq.subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.mul_ww)


if __name__ == '__main__':
    run()
# created on 2018-11-10
# updated on 2023-04-05
