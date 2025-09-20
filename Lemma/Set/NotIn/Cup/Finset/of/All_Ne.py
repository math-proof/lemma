from util import *


@apply
def apply(given):
    (xi, y), (i, S[0], n) = given.of(All[Unequal])
    if not xi._has(i):
        xi, y = y, xi

    x = Stack[i:n](xi).simplify()

    return NotElement(y, x.cup_finiteset())


@prove
def prove(Eq):
    from Lemma import Set

    i = Symbol(integer=True)
    y = Symbol(real=True, given=True)
    x = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(All[i:n](Unequal(x[i], y)))

    Eq << ~Eq[-1]

    Eq << Set.Any_In.of.In_Cup.apply(Eq[-1])
    Eq << Eq[-1].this.expr.reversed

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2021-01-14
