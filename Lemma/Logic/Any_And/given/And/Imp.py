from util import *


@apply
def apply(imply):
    eqs, *limits = imply.of(Any[And])
    ps, qs = zip(*(eq.of(Imply) for eq in eqs))

    cond = S.false
    for i in range(len(ps)):
        cond |= ps[i]
        for j in range(i):
            if ps[i] & ps[j] == False:
                continue
            return

    assert cond

    variables = [v for v, *_ in limits]
    infers = []
    for p, q  in zip(ps, qs):
        assert not p.has(*variables)
        infers.append(Imply(p, Any(q, *limits)))

    return tuple(infers)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    p, q = Function(bool=True)
    Eq << apply(Any[x](Imply(j < i, p(x[i, j])) & Imply(j >= i, q(x[i, j]))))

    Eq <<= Logic.Imp.And.of.Imp.apply(Eq[-2]), Logic.Imp.And.of.Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Logic.Any_And.of.Any.All, simplify=None), Eq[-1].this.rhs.apply(Logic.Any_And.of.Any.All, simplify=None)

    Eq << Logic.ImpOrS.of.Imp.Imp.apply(Eq[-2], Eq[-1])

    Eq << Eq[0].this.find(Imply).apply(Logic.Imp.Is.Or_Not)

    Eq << Eq[-1].this.find(Imply).apply(Logic.Imp.Is.Or_Not)

    Eq << Eq[-1].this.find(And).apply(Logic.And_Or.Is.OrAndS)

    Eq << Logic.Any_Or.given.OrAnyS.apply(Eq[-1])

    Eq << Eq[-1].this.find(And[Or]).apply(Logic.And_Or.Is.OrAndS)

    Eq << Eq[-1].this.find(Any[Or]).apply(Logic.Any_Or.given.OrAnyS)

    Eq << Eq[-1].this.args[:2].apply(Algebra.Or_Any.given.Any.Or)

    Eq << Logic.Or.given.Cond.apply(Eq[-1], 1)




if __name__ == '__main__':
    run()
# created on 2023-07-01
