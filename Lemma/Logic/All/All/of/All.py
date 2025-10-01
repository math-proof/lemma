from util import *


def split(All, given, cond, wrt):
    from Lemma.Algebra.Sum.eq.AddSumS import split

    if isinstance(cond, Boolean):
        if wrt is None:
            wrt = cond.wrt

        cond = wrt.domain_conditioned(cond)

        if wrt not in given.variables:
            domain = given.domain_defined(wrt)
            function, *limits = given.of(All)
            given = All(function, *limits, (wrt, domain))

    return split(All, given, cond, wrt=wrt)


@apply
def apply(given, *, cond=None, wrt=None):
    given = split(All, given, cond, wrt)
    return given.of(And)


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(real=True)
    f = Function(integer=True, shape=())
    d = Symbol(real=True, positive=True)
    Eq << apply(All[x:Interval(-d, d, left_open=True, right_open=True)](f(x) > 0), cond=x < 0)

    Eq << Set.AllIn_SDiff.of.All.apply(Eq[0], domain=Interval(0, d, right_open=True))

    Eq << Set.AllIn_SDiff.of.All.apply(Eq[0], domain=Interval(-d, 0, right_open=True, left_open=True))





if __name__ == '__main__':
    run()

# created on 2018-04-01
# updated on 2023-10-22
