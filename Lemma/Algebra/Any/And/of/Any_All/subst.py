from util import *


@apply
def apply(given, old, new):
    new = sympify(new)
    from sympy.concrete.limits import limits_dict
    (function, *limits_f), *limits_e = given.of(Any[All])
    limits_f_dict = limits_dict(limits_f)

    domain = limits_f_dict[old]
    if domain:
        assert new in domain

    return Any(All(function._subs(old, new) & function, *limits_f), *limits_e)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    C, x, y = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    x0 = Symbol(domain=A)
    f = Function(integer=True)
    Eq << apply(Any[C](All[x:A](f(x, C) > 0)), x, x0)

    Eq << Eq[-1].this.expr.apply(Logic.All_And.given.All.All)

    Eq << Eq[-1].this.find(Or).apply(Logic.Or.given.Cond, 1)

    Eq << Eq[0].this.expr.apply(Algebra.Cond.of.All.subst, x, x0, ret=0)




if __name__ == '__main__':
    run()
# created on 2019-02-25
