from util import *


@apply
def apply(given, x=None, k=None):
    S, n = given.of(Equal[Card])
    if k is None:
        k = S.generate_var(integer=True)
    kwargs = S.etype.dict
    shape = (oo,)
    if x is None:
        x = S.generate_var(shape=shape, **kwargs)
    return Any[x[:n]:All[k:1:n](x[k - 1] < x[k])](Equal(S, Cup[k:n]({x[k]})))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(real=True, shape=(oo,))
    S = Symbol(etype=dtype.real)
    Eq << apply(Equal(Card(S), n), x, i)

    Eq << Set.Any.Eq.of.Eq_Card.apply(Eq[0], x)

    Eq << Bool.Any_And.of.AnySetOf_AnySetOf.apply(Eq[-1])

    Eq << Bool.AnySetOf.of.Any_And.apply(Eq[-1], 0)

    Eq << Eq[-1].this.expr.apply(Set.Any.Eq.Cup.Finset.of.All_Ne)

    Eq << Bool.Any_And.of.AnySetOf_AnySetOf.apply(Eq[-1], 1)

    Eq << Eq[-1].this.expr.apply(Bool.Eq.of.Eq.Eq)







if __name__ == '__main__':
    run()
# created on 2023-11-11
# updated on 2023-11-12
