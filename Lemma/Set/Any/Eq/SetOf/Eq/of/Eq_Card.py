from util import *


@apply
def apply(given, x=None):
    S, n = given.of(Equal[Card])
    assert n > 0
    i = S.generate_var(integer=True)
    kwargs = S.etype.dict
    if 'shape' in kwargs:
        shape = (oo,) + kwargs['shape']
    else:
        shape = (oo,)
    kwargs.pop('shape', None)
    if x is None:
        x = S.generate_var(shape=shape, **kwargs)
    return Any[x[:n]:Equal(Card(x[:n].cup_finiteset()), n)](Equal(S, Cup[i:n]({x[i]})))


@prove
def prove(Eq):
    from Lemma import Set

    n, k = Symbol(integer=True, positive=True)
    S = Symbol(etype=dtype.integer[k])
    Eq << apply(Equal(Card(S), n))

    Eq << Set.Any.Eq.of.Eq_Card.apply(Eq[0])



    Eq << Eq[-1].this.limits[0][1].apply(Set.Eq.Card.Cup.Finset.of.All_Ne)




if __name__ == '__main__':
    run()
# created on 2021-02-02
# updated on 2023-11-11
