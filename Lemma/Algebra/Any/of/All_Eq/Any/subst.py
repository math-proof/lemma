from util import *


@apply
def apply(eq, any, reverse=False):
    (lhs, rhs), *limits_f = eq.of(All[Equal])
    f_eq, *limits_e = any.of(Any)

    assert limits_f == limits_e
    if reverse:
        lhs, rhs = rhs, lhs

    return Any(f_eq._subs(lhs, rhs), *limits_f)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    m, n = Symbol(integer=True, positive=True)

    a, b, c = Symbol(real=True, shape=(m, n))

    f = Function(real=True)

    C, S = Symbol(etype=dtype.real[m][n])

    Eq << apply(All[c:C](Equal(a, f(c))), Any[c:C](Element(a * b + c, S)))

    Eq << Logic.Any_And.of.Any.All.All_Imp.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subst)


if __name__ == '__main__':
    run()
# created on 2019-01-06
