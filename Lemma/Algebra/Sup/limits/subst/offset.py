from util import *


@apply
def apply(self, index=0, offset=None):
    from Lemma.Algebra.Sum.limits.subst.offset import limits_subs
    return Equal(self, limits_subs(Sup, self, index, offset), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a, b, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:a:b](f(x)), t)

    y = Symbol(Eq[-1].lhs)
    Eq << y.this.definition

    Eq << Eq[-1].reversed

    Eq <<= Algebra.And.of.Eq.squeeze.apply(Eq[-1]), Eq[0].reversed.subs(Eq[-1])

    Eq <<= Algebra.All.Le.of.LeSup.apply(Eq[-3]), Algebra.All.Any.Gt.of.GeSup.apply(Eq[-2]), Algebra.Eq.given.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.LeSup.given.All.Le.apply(Eq[-2]), Algebra.GeSup.given.All_Any_Gt.apply(Eq[-1])

    Eq << Algebra.All.given.All.limits.subst.offset.apply(Eq[-2], -t)
    Eq << Eq[-1].this.expr.apply(Algebra.Any.given.Any.limits.subst.offset, -t)




if __name__ == '__main__':
    run()
# created on 2019-08-29
