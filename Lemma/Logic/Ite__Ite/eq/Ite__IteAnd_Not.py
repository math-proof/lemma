from util import *


@apply
def apply(piecewise, i=0, offset=1, evaluate=False):
    [*ec] = piecewise.of(Piecewise)

    _, cond = ec[i]
    assert offset > 0
    j = i + offset

    expr_next, cond_next = ec[j]
    cond_next &= cond.invert()

    ec[j] = (expr_next, cond_next)

    if ec[-1][1]:
        ...
    else:
        ec[-1][1] = True

    return Equal(piecewise, piecewise.func(*ec, evaluate=evaluate))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,))
    A, B = Symbol(etype=dtype.real[k])
    g, f, h = Function(shape=(), real=True)
    Eq << apply(Piecewise((g(x), Element(x, A)), (f(x), NotElement(x, B)), (h(x), True)))

    p = Symbol(Eq[0].lhs)
    Eq << p.this.definition

    Eq << Logic.OrAndS.of.BFn_Ite.apply(Eq[-1])

    Eq << Logic.BFn_Ite__Ite.of.And.ou.OrAndS.apply(Eq[-1], wrt=p)

    Eq << Eq[-1].this.lhs.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, -2)

    Eq << Eq[-1].this.lhs.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, 0)

    Eq << Eq[-1].this.lhs.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, 0)
    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[1], Eq[-1])





if __name__ == '__main__':
    run()

# created on 2018-01-30
# updated on 2023-05-20
