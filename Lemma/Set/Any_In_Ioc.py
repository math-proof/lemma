from util import *


@apply
def apply(x, n=None):
    if n is None:
        n = x.generate_var(integer=True)
    assert x.is_real
    return Any[n](Element(n, Interval(x - 1, x, left_open=True)))


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(x, n)

    Eq << Eq[-1].this.expr.apply(Set.In_Ico.given.Le.Lt)

    Eq << Eq[-1].this.find(Greater) + 1

    Eq << Eq[-1].this.expr.apply(Set.Gt.Le.given.In)

    Eq << Set.Any_In_Ico.apply(x, n)


if __name__ == '__main__':
    run()

# created on 2021-04-21
