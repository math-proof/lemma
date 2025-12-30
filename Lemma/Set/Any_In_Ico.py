from util import *


@apply
def apply(x, k=None):
    assert x.is_real
    if k is None:
        k = x.generate_var(integer=True, var='k')

    return Any[k](Element(x, Interval(k, k + 1, right_open=True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x = Symbol(real=True, given=True)
    Eq << apply(x)

    Eq << Algebra.Any.given.Cond.subst.apply(Eq[0], Eq[0].variable, Floor(x))

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[-1])

    Eq << Algebra.Lt_Add_.Floor.One.apply(x)

    Eq << Algebra.Ge_Floor.apply(x)


if __name__ == '__main__':
    run()

# created on 2019-12-04
