from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    assert x.is_finite
    return Element(x, Interval(-oo, oo))


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(complex=True)
    Eq << apply(x > 0)

    Eq << Set.IsReal.of.Gt.apply(Eq[0], simplify=None)


if __name__ == '__main__':
    run()
# created on 2020-04-02

