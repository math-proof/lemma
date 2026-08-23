from util import *


@apply
def apply(given, delta=None, var=None):
    from Lemma.Real.Any.All.of.IsLimited.limit_definition import of_limited
    from Lemma.Real.EqLim.Is.All_Any_All import Any_All
    fn, (x, x0) = of_limited(given, real=True)

    M = fn.generate_var(excludes={x}, var=var, positive=True, real=True)
    exists = Any_All(Equal(given.lhs, S.Zero), M, delta=delta)

    limits = exists.limits + (M,)
    return exists.func(exists.expr, *limits)


@prove
def prove(Eq):
    from Lemma import Real, Algebra, Bool, Int

    n = Symbol(integer=True, positive=True)
    x, x0, a = Symbol(real=True)
    f = Function(real=True, shape=())
    Eq << apply(Element(Limit[x:x0 + S.Infinitesimal](f(x)), Reals), var='M')

    M = Eq[-1].variables[1]
    Eq << Real.Any.All.of.IsLimited.limit_definition.symbol_subs.apply(Eq[0], var='A')

    A = -Eq[-1].expr.expr.lhs.arg.args[0]
    Eq << Eq[-1].this.expr.expr.apply(Int.And.of.Lt.split.Abs)

    Eq << Eq[-1].this.expr.expr.args[0] + A

    Eq << Eq[-1].this.expr.expr.args[1] + A

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.Abs.Max.of.Lt.Gt)

    Eq << Bool.Any_UFn.of.UFnUFn.apply(Eq[-1], Eq[-1].expr.expr.rhs, M)


if __name__ == '__main__':
    run()
# created on 2020-04-09
# updated on 2023-05-20
