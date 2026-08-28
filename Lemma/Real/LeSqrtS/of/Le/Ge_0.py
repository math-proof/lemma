from util import *


@apply
def apply(is_nonnegative, le):
    x = is_nonnegative.of(Expr >= 0)
    S[x], y = le.of(Expr <= Expr)

    return LessEqual(sqrt(x), sqrt(y))


@prove
def prove(Eq):
    from Lemma import Set, Bool, Nat, Real

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, LessEqual(x, y))

    Eq << Real.GeSqrt_0.pos.apply(Eq[0])

    t = Symbol(nonnegative=True)
    Eq << Nat.Gt.ou.AndGeS.of.Ge.apply(Eq[-1], t)

    Eq.ou = Eq[-1].subs(t, sqrt(y))

    Eq << Nat.Ge.of.Le.Ge.apply(Eq[1], Eq[0])

    Eq << Real.GeSqrt_0.pos.apply(Eq[-1])

    Eq << Set.In_Ici.of.Ge.apply(Eq[-1])

    Eq << Bool.BFn.of.BFnIte.Cond.apply(Eq[-1], Eq.ou, invert=True)

    Eq << Eq[-1].this.find(Greater).apply(Nat.GtSquareS.of.Gt.Ge_0)

    Eq << Bool.BFn.of.BFnIte.Cond.apply(Eq[1], Eq[-1], invert=True)

    Eq << Bool.Cond.of.And.apply(Eq[-1], 0)




if __name__ == '__main__':
    run()
# created on 2018-07-07
# updated on 2023-05-14
