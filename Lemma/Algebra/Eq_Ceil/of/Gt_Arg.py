from util import *


@apply
def apply(gt):
    A, B = gt.of(Arg + Arg > Pi)
    return Equal(Ceil((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 1)


@prove
def prove(Eq):
    from Lemma import Set

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Arg(A) + Arg(B) > S.Pi)

    Eq <<= Set.Arg.In.IocNegPiPi.apply(A), Set.Arg.In.IocNegPiPi.apply(B)

    Eq << Set.Add.In.Ioc.of.In.In.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Set.InDiv.of.In_Icc.apply(Eq[-1], S.Pi * 2)

    Eq << Eq[0] / (S.Pi * 2)

    Eq << Set.In.Icc.Inter.of.Gt.In_Icc.apply(Eq[-1], Eq[-2])

    Eq << Set.InSub.of.In_Icc.apply(Eq[-1], S.One / 2)
    Eq << Set.In_Range.Ceil.of.In_Icc.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-10-27
