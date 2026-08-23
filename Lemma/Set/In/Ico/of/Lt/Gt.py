from util import *


@apply
def apply(greater_than, _greater_than):
    x, a = greater_than.of(Less)
    _x, b = _greater_than.of(Greater)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,

    assert x.is_integer
    return Element(x, Range(b + 1, a))


@prove
def prove(Eq):
    from Lemma import Set, Nat

    a, b, x = Symbol(integer=True, given=True)
    # Eq << apply(b < x, a >= x)
    Eq << apply(x < b, x > a)

    Eq << Set.In_Ico.given.Ge.Le_Sub_1.apply(Eq[-1])



    Eq << Nat.Ge.given.Gt.relax.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-05-29
