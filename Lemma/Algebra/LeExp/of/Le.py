from util import *


@apply
def apply(given):
    lhs, rhs = given.of(LessEqual)

    return LessEqual(exp(lhs), exp(rhs))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y = Symbol(real=True)
    Eq << apply(LessEqual(x, y))

    t = Symbol(y - x)
    Eq << t.this.definition

    Eq << Algebra.Ge_0.of.Le.apply(Eq[0])

    Eq.ge_zero = Algebra.Ge.of.Eq.Ge.subst.apply(Eq[-2], Eq[-1])

    Eq << Eq[-2] + x

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Eq[-1] / exp(x)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Exp)

    r = Symbol(nonnegative=True)
    Eq << GreaterEqual(exp(r), 1, plausible=True)

    Eq << Bool.All.of.Cond.apply(Eq[-1])

    Eq << Bool.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-1].find(Symbol), t)

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq.ge_zero, Eq[-1])



if __name__ == '__main__':
    run()
# created on 2022-04-01
