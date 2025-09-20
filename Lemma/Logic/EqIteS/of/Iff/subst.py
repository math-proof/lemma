from util import *


@apply
def apply(given, expr):
    fn, fn1 = given.of(Iff)
    return Equal(expr, expr._subs(fn, fn1))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x, y = Symbol(integer=True)
    f, g, h = Function(integer=True)

    Eq << apply(Iff(x > y, f(x) > f(y)), Piecewise((g(x, y), x > y), (h(x, y), True)))

    Eq << Logic.EqBoolS.of.Iff.apply(Eq[0])

    Eq << Eq[1].lhs._subs(x > y, Equal(Bool(x > y), 1)).this.args[0].cond.lhs.apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.lhs.subs(Eq[-2])

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].reversed

if __name__ == '__main__':
    run()


# created on 2018-02-03
