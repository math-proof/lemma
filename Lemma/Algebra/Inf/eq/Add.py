from util import *


@apply
def apply(self):
    expr, *limits = self.of(Inf)
    vars = [x for x, *ab in limits]

    args, const = std.array_split(expr.of(Add), lambda arg : arg.has(*vars))
    assert const

    const = Add(*const)
    expr = Add(*args)

    return Equal(self, const + Inf(expr, *limits))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, m, M, h = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:m:M](f(x) + h))

    y = Symbol(Eq[0].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq <<= Algebra.And.of.Eq.squeeze.apply(Eq[-1]), Eq[0].subs(Eq[-1])

    z = Symbol(real=True)
    Eq <<= Algebra.All.Any.Lt.of.LeInf.apply(Eq[-3], z), Algebra.All.Ge.of.GeInf.apply(Eq[-2]), Algebra.Eq.given.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.LeInf.given.All_Any_Lt.apply(Eq[-2], z), Algebra.GeInf.given.All.Ge.apply(Eq[-1])

    Eq << Algebra.All.given.All.limits.subst.offset.apply(Eq[-1], h)

    Eq << Eq[-1].this.expr.expr - h


if __name__ == '__main__':
    run()
# created on 2019-08-26
