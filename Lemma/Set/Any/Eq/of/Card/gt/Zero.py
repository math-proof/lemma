from util import *


@apply
def apply(given, x=None):
    S = given.of(Card > 0)
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
    from Lemma import Set, Algebra, Bool

    k = Symbol(integer=True, positive=True)
    s = Symbol(etype=dtype.integer[k], given=True)
    Eq << apply(Card(s) > 0)

    Eq << Set.In.Ico.of.Gt.apply(Eq[0])

    m = Symbol(integer=True, positive=True)
    Eq << Set.Any.Eq.of.In.apply(Eq[-1], var=m)

    Eq << Eq[-1].this.expr.apply(Set.Any.And.of.Eq_Card, simplify=None)

    Eq << Eq[-1].this.expr.apply(Bool.UFn.of.UFn.Eq, swap=True, reverse=True, simplify=None, ret=1)

    Eq << Bool.AnySetOf.of.Any_And.apply(Eq[-1], 1)

    Eq << Set.EqInter.of.In.apply(Eq[2])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.apply(Algebra.Any.limits.separate, simplify=None)

    Eq << Eq[-1].this.apply(Algebra.Any.Is.Or.doit.setlimit)





if __name__ == '__main__':
    run()
# created on 2021-02-03
# updated on 2023-11-17
