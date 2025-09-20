from util import *


@apply
def apply(x, k=None):
    assert x.is_real
    if k is None:
        k = x.generate_var(integer=True, var='k')

    return Any[k](Element(x, Interval(k, k + 1, left_open=True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x = Symbol(real=True, given=True)
    Eq << apply(x)

    Eq << Algebra.Any.given.Cond.subst.apply(Eq[0], Eq[0].variable, Ceil(x) - 1)

    Eq << Set.In_Ico.given.Ge.Lt.apply(Eq[-1])

    Eq << Algebra.Gt_Sub_.Ceil.One.apply(x)

    Eq << Algebra.Le_Ceil.apply(x)


if __name__ == '__main__':
    run()
# created on 2018-10-29
