from util import *


@apply
def apply(given, x=None):
    fx, rhs = given.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs

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
    # arg_AB = Ceil(3 * Arg(A * B) / (S.Pi * 2) - S.One / 2)
    arg_AB = Piecewise((0, Equal(p * Ceil((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True))
    d = arg_p - arg_AB

    return Imply(Equal(d, 0), Or(Equal(x, A + B - a / 3), Equal(x, A * w + B * ~w - a / 3), Equal(x, A * ~w + B * w - a / 3))), \
            Imply(Equal(d % 3, 1), Or(Equal(x, A * w + B - a / 3), Equal(x, A * ~w + B * ~w - a / 3), Equal(x, A + B * w - a / 3))), \
            Imply(Equal(d % 3, 2), Or(Equal(x, A * ~w + B - a / 3), Equal(x, A + B * ~w - a / 3), Equal(x, A * w + B * w - a / 3)))


@prove
def prove(Eq):
    from Lemma import Algebra, Int

    x, a, b, c = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 3 + a * x ** 2 + b * x + c, 0), x=x)

    x = Symbol(x + a / 3)
    Eq.x_def = x.this.definition

    Eq << Eq.x_def.this.apply(Int.EqAdd.Is.Eq_Sub, rhs=1).reversed

    Eq << Eq[0].subs(Eq[-1])

    Eq << Eq[-1].this.find(Pow[Add]).apply(Algebra.Pow.eq.Add, simplify=None)

    Eq << Eq[-1].this.find(Pow[Add]).apply(Algebra.Pow.eq.Add, simplify=None)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS, simplify=None)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS, simplify=None)

    Eq << Algebra.And.Imp.Or.Eq.of.Add.eq.Zero.cubic.depressed.apply(Eq[-1], x=x)

    Eq <<= Eq[-3].subs(Eq.x_def), Eq[-2].subs(Eq.x_def), Eq[-1].subs(Eq.x_def)

    Eq <<= Eq[-3].this.find(Equal[Add, Add]).apply(Int.EqAdd.Is.Eq_Sub, lhs=-1), Eq[-2].this.find(Equal[Add, Add]).apply(Int.EqAdd.Is.Eq_Sub, lhs=-1), Eq[-1].this.find(Equal[Add, Add]).apply(Int.EqAdd.Is.Eq_Sub, lhs=-1)

    Eq <<= Eq[-3].this.find(Equal[Add, Add]).apply(Int.EqAdd.Is.Eq_Sub, lhs=-1), Eq[-2].this.find(Equal[Add, Add]).apply(Int.EqAdd.Is.Eq_Sub, lhs=-1), Eq[-1].this.find(Equal[Add, Add]).apply(Int.EqAdd.Is.Eq_Sub, lhs=-1)

    Eq <<= Eq[-3].this.find(Equal[Add, Add]).apply(Int.EqAdd.Is.Eq_Sub, lhs=-1), Eq[-2].this.find(Equal[Add, Add]).apply(Int.EqAdd.Is.Eq_Sub, lhs=-1), Eq[-1].this.find(Equal[Add, Add]).apply(Int.EqAdd.Is.Eq_Sub, lhs=-1)





if __name__ == '__main__':
    run()
# created on 2018-11-25
# updated on 2023-05-20
