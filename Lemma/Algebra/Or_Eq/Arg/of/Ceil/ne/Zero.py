from util import *


@apply
def apply(is_nonzero):
    ceil = is_nonzero.of(Unequal[0])
    ((A, B), S[S.One / (S.Pi * 2)]), S[S.One  / 2] = ceil.of(Ceil[(Arg + Arg) * Expr - Expr])
    return Equal(ceil, 1) | Equal(ceil, -1)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Unequal(Ceil((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 0))

    Eq <<= Set.Arg.In.IocNegPiPi.apply(A), Set.Arg.In.IocNegPiPi.apply(B)

    Eq << Set.Add.In.Ioc.of.In.In.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Set.InDiv.of.In_Icc.apply(Eq[-1], S.Pi * 2)

    Eq << Set.InSub.of.In_Icc.apply(Eq[-1], S.One / 2)

    Eq << Set.In_Ico.Ceil.of.In_Icc.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Set.Ico.eq.Finset)

    Eq << Set.Or.Eq.of.In_Finset.apply(Eq[-1])

    Eq << Bool.Cond.of.Or_Not.Cond.apply(Eq[0], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2018-10-24
