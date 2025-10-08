from util import *


@apply
def apply(piecewise, i=0, offset=1, evaluate=False):
    [*ec] = piecewise.of(Piecewise)

    _, cond = ec[i]
    assert offset > 0
    j = i + offset

    expr_next, cond_next = ec[j]
    cond_next |= cond

    ec[j] = (expr_next, cond_next)

    if ec[-1][1]:
        ...
    else:
        ec[-1][1] = True

    return Equal(piecewise, piecewise.func(*ec, evaluate=evaluate))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,))
    A, B = Symbol(etype=dtype.real[k])
    g, f, h = Function(shape=(), real=True)
    Eq << apply(Piecewise((g(x), Element(x, A)), (f(x), NotElement(x, A | B)), (h(x), True)))


    Eq << Eq[0].this.rhs.apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not)



if __name__ == '__main__':
    run()
# created on 2023-05-10
