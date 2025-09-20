from util import *



def transit(b_eq_x, x_eq_a, reverse=False):
    b, x = b_eq_x.of(Iff)
    _x, a = x_eq_a.of(Iff)
    if x != _x:
        if _x == b:
            b, x = x, b
        elif a == b:
            b, x, _x, a = x, b, a, _x
        elif x == a:
            _x, a = a, _x

        assert x == _x

    if reverse:
        b, a = a, b
    return Iff(b, a)


@apply
def apply(equivalent_0, equivalent_1, reverse=False):
    return transit(equivalent_0, equivalent_1, reverse=reverse)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, x, b = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Iff(f(b) > 0, f(x) > 0), Iff(f(x) > 0, f(a) > 0))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Logic.Imp.of.Iff.apply(Eq[0])

    Eq << Logic.Imp.of.Iff.apply(Eq[1])

    Eq << Logic.Imp.of.Imp.Imp.apply(Eq[-2], Eq[-1])

    Eq << Logic.Imp.of.Iff.apply(Eq[0], reverse=True)

    Eq << Logic.Imp.of.Iff.apply(Eq[1], reverse=True)

    Eq << Algebra.Given.of.Given.Given.apply(Eq[-2], Eq[-1]).reversed




if __name__ == '__main__':
    run()
# created on 2019-09-12

# updated on 2025-04-12
