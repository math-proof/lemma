from util import *


@apply
def apply(given, index=0):
    args = []
    for arg in given.of(Equal[Add, 0]):
        arg = arg.of(Expr ** 2)
        assert arg.is_extended_real
        args.append(arg)

    return Equal(args[index], 0)


@prove
def prove(Eq):
    from Lemma import Int, Nat

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Equal(x * x + y * y + z * z, 0))

    Eq << ~Eq[1]

    Eq << Int.GtAbs_0.of.Ne_0.apply(Eq[-1])

    Eq << Nat.GtSquare_0.of.Gt_0.apply(Eq[-1])

    Eq << Nat.Le0AddAddSquareSMulMul2.apply(y)

    Eq << Nat.Le0AddAddSquareSMulMul2.apply(z)

    Eq << Nat.Le0Add.of.Ge_0.Ge_0.apply(Eq[-1], Eq[-2])

    Eq << Nat.Lt0Add.of.Ge_0.Gt_0.apply(Eq[-1], Eq[-4])

    Eq << Eq[-1].subs(Eq[0])




if __name__ == '__main__':
    run()
# created on 2018-06-08
# updated on 2022-01-07
