from util import *


@apply
def apply(self, index=0, offset=None):
    from Lemma.Finset.SumIco.eq.Sum_UFnAdd import limits_subs
    return Equal(self, limits_subs(Sup, self, index, offset), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Real, Nat

    x, a, b, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:a:b](f(x)), t)

    y = Symbol(Eq[-1].lhs)
    Eq << y.this.definition

    Eq << Eq[-1].reversed

    Eq <<= Nat.And.of.Eq.squeeze.apply(Eq[-1]), Eq[0].reversed.subs(Eq[-1])

    Eq <<= Real.All.Le.of.LeSup.apply(Eq[-3]), Real.All.Any.Gt.of.GeSup.apply(Eq[-2]), Nat.Eq.given.And.squeeze.apply(Eq[-1])

    Eq <<= Real.LeSup.given.All.Le.apply(Eq[-2]), Real.GeSup.given.All_Any_Gt.apply(Eq[-1])

    Eq << Nat.All.given.All.limits.subst.offset.apply(Eq[-2], -t)
    Eq << Eq[-1].this.expr.apply(Nat.Any.given.Any.limits.subst.offset, -t)




if __name__ == '__main__':
    run()
# created on 2019-08-29
