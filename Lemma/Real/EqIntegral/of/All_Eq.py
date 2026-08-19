from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Equal])

    return Equal(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra
    x, a, b = Symbol(real=True)
    f, g = Function(shape=(), real=True)

    Eq << apply(All[x:a:b](Equal(f(x), g(x))))

    x_ = Symbol('x', domain=Interval.open(a, b))

    Eq << Algebra.Cond.of.All.subst.apply(Eq[0], x, x_)

    Eq << Eq[1].this.lhs.limits_subs(x, x_)

    Eq << Eq[-1].this.rhs.limits_subs(x, x_)

    Eq << Eq[-1].this.lhs.subs(Eq[2])


if __name__ == '__main__':
    run()

# created on 2020-03-29
