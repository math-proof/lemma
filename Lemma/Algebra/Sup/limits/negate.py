from util import *


@apply
def apply(self):
    expr, (x, *ab) = self.of(Sup)
    if len(ab) == 2:
        a, b = ab
        if x.is_integer:
            limit = (x, 1 - b, 1 - a)
        else:
            limit = (x, -b, -a)
    else:
        domain, = ab
        limit = (x, -domain)

    return Equal(self, Sup(expr._subs(x, -x), limit))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:a:b](f(x)))

    y = Symbol(Eq[0].lhs)
    Eq << y.this.definition.reversed

    Eq << Algebra.And.of.Eq.squeeze.apply(Eq[-1])

    Eq <<= Algebra.All.Le.of.LeSup.apply(Eq[-2]), Algebra.All.Any.Gt.of.GeSup.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[1]).reversed

    Eq << Algebra.Eq.given.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.LeSup.given.All.Le.apply(Eq[-2]), Algebra.GeSup.given.All_Any_Gt.apply(Eq[-1])

    Eq <<= Eq[-2].this.apply(Algebra.All.limits.Neg), Eq[-1].this.expr.apply(Algebra.Any.limits.Neg)


if __name__ == '__main__':
    run()
# created on 2020-03-28
