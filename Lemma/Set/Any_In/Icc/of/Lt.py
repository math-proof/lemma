from util import *


@apply
def apply(given, x=None, left_open=True, right_open=True):
    a, b = given.of(Less)
    if x is None:
        x = given.generate_var(var='x', real=True)

    assert left_open or right_open
    return Any[x](Element(x, Interval(a, b, left_open=left_open, right_open=right_open)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    a, b = Symbol(real=True, given=True)
    Eq << apply(a < b)

    x = Eq[1].variable
    Eq << Algebra.Any.given.Cond.subst.apply(Eq[-1], x, (a + b) / 2)

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[-1])

    Eq <<= Eq[-2] * 2, Eq[-1] * 2

    Eq <<= Eq[-1] - b, Eq[-2] - a

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-12-23
