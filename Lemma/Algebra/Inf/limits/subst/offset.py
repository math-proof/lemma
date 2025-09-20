from util import *


@apply
def apply(self, index=0, offset=None):
    from Lemma.Algebra.Sum.limits.subst.offset import limits_subs
    return Equal(self, limits_subs(Inf, self, index, offset), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a, b, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:a:b](f(x)), t)

    y = Symbol(Eq[-1].lhs)
    Eq << y.this.definition

    Eq << Eq[-1].reversed

    Eq <<= Algebra.And.of.Eq.squeeze.apply(Eq[-1]), Eq[0].reversed.subs(Eq[-1])

    Eq <<= Algebra.All.Any.Lt.of.LeInf.apply(Eq[-3]), Algebra.All.Ge.of.GeInf.apply(Eq[-2]), Algebra.Eq.given.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.LeInf.given.All_Any_Lt.apply(Eq[-2]), Algebra.GeInf.given.All.Ge.apply(Eq[-1])

    Eq << Eq[-2].this.expr.apply(Algebra.Any.given.Any.limits.subst.offset, -t)
    Eq << Algebra.All.given.All.limits.subst.offset.apply(Eq[-1], -t)



if __name__ == '__main__':
    run()
# created on 2019-10-03
