from util import *


@apply
def apply(cup_finiteset_equality, last_element_equality):
    (p, n), S[n] = last_element_equality.of(Equal[Indexed])

    lhs = cup_finiteset_equality.of(Equal[Range(n)])
    assert lhs._dummy_eq(p[:n].cup_finiteset())

    return Equal(p[:n + 1].cup_finiteset(), Range(n + 1))


@prove
def prove(Eq):
    from Lemma import Set

    n = Symbol(integer=True, positive=True, given=True)
    p = Symbol(shape=(oo,), integer=True, nonnegative=True, given=True)
    Eq << apply(Equal(p[:n].cup_finiteset(), Range(n)),
                Equal(p[n], n))

    Eq << Eq[-1].this.lhs.apply(Set.Cup.eq.UnionCupS, cond=slice(-1))

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2020-07-08
