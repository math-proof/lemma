from util import *


@apply
def apply(given, x=None):
    S = given.of(Unequal[Card, 0])
    n = Card(S)
    i = S.generate_var(integer=True)
    kwargs = S.etype.dict
    if 'shape' in kwargs:
        shape = (oo,) + kwargs['shape']
    else:
        shape = (oo,)
    kwargs.pop('shape', None)
    if x is None:
        x = S.generate_var(shape=shape, **kwargs)
    return Any[x[:n]](Equal(S, Cup[i:n]({x[i]})))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    k = Symbol(integer=True, positive=True)
    s = Symbol(etype=dtype.integer[k], given=True)
    Eq << apply(Unequal(Card(s), 0))

    Eq << Algebra.Gt_0.of.Ne_0.apply(Eq[0])

    Eq << Set.Any.Eq.of.Card.gt.Zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-02-03
