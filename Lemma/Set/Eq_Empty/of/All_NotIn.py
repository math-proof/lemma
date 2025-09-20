from util import *


@apply
def apply(given):
    e, s = given.of(NotElement)
    return Equal(s, e.emptySet)


@prove
def prove(Eq):
    from Lemma import Set
    s = Symbol(etype=dtype.integer, given=True)
    e = Symbol(integer=True, given=True)

    Eq << apply(NotElement(e, s))

    U = Symbol(e.universalSet)

    Eq << All[e:U](NotElement(e, s), plausible=True)

    Eq << Eq[-1].this.limits[0][1].definition

    Eq << Set.Inter.eq.Empty.of.All_NotIn.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.args[0].definition


if __name__ == '__main__':
    run()

# created on 2018-03-05

