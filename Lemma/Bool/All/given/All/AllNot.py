from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    assert cond.is_bool

    if wrt is None:
        wrt = cond.wrt

    assert not wrt.is_given

    if wrt.is_bounded:
        from Lemma.Bool.All.of.Cond import all
        given = all(given, wrt)
    else:
        given = All(given, (wrt,))
    assert given.is_ForAll

    domain = wrt.domain_conditioned(cond)
    if not domain.is_integer:
        domain = wrt.domain_conditioned(cond)

    from Lemma.Algebra.Sum.eq.AddSumS import split
    given = split(All, given, wrt.domain_conditioned(cond))
    if given.is_And:
        lhs, rhs = given.of(And)
        return lhs, rhs
    return given


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    e = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq << Bool.AllOr.of.All.All.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

# created on 2018-09-05
