from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)

    return Equal(Inf(lhs, *limits).simplify(), Inf(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n))
    f, g = Function(real=True)
    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    i_ = Eq[1].lhs.variable
    Eq << Eq[1].this.lhs.limits_subs(i_, i)

    Eq << Eq[-1].this.rhs.limits_subs(i_, i)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2021-08-01

