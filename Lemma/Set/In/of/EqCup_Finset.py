from util import *


@apply
def apply(given, index=None):
    from Lemma.Set.Eq.given.Eq.Cup.Finset import of_cup_finiteset
    cup, s = given.of(Equal)
    x = of_cup_finiteset(cup)
    n = x.shape[0]
    assert 0 <= index < n
    return Element(x[index], s)


@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(integer=True)
    s = Symbol('A', etype=dtype.integer)
    x = Symbol(integer=True, shape=(oo,))
    i = Symbol(domain=Range(n))

    Eq << apply(Equal(x[:n].cup_finiteset(), s), index=i)

    Eq << Element(x[i], x[:n].cup_finiteset(), plausible=True)

    Eq << Eq[-1].this.rhs.apply(Set.Cup.eq.UnionCupS, cond={i})

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-08-04
