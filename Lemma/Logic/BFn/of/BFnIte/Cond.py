from util import *


def process_given_conditions(eq, f_eq, invert=None, reverse=False, swap=False):
    if swap:
        f_eq, eq = eq, f_eq

    assert eq.is_Boolean
    assert f_eq.is_Boolean

    eq_original = eq
    if invert:
        eq = eq.invert()
        substituent = S.BooleanFalse
    else:
        substituent = S.BooleanTrue

    if reverse:
        eq = eq.reversed

    return eq_original, f_eq._subs(eq, substituent)


@apply
def apply(cond_0, cond_1, **kwargs):
    eq, f_eq = process_given_conditions(cond_0, cond_1, **kwargs)
    return f_eq


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)
    f, g, h = Function(shape=(), integer=True)

    Eq << apply(NotElement(x, S), Equal(Piecewise((f(x), NotElement(x, S)), (g(x), True)), h(x)))

    Eq << Equal(Bool(NotElement(x, S)), 1, plausible=True)

    Eq << Eq[-1].this.lhs.apply(Logic.Bool.eq.Ite)

    Eq << Equal(Piecewise((f(x), Equal(Bool(NotElement(x, S)), 1)), (g(x), True)), h(x), plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[1].this.lhs.simplify()

    Eq << Eq[-2].subs(Eq[-3])


if __name__ == '__main__':
    run()

# created on 2018-01-06
