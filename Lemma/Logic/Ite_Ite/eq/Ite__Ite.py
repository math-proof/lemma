from util import *


def flatten(piecewise, index=None):
    if index is None:
        for index, (e, c) in enumerate(piecewise.args):
            if e.is_Piecewise:
                break
        else:
            return piecewise

        _piecewise = flatten(piecewise, index)
        if _piecewise is piecewise:
            return piecewise
        return flatten(_piecewise)

    expr, cond = piecewise.args[index]
    _ec = expr.of(Piecewise)

    _ec = tuple((e, c & cond) for e, c in _ec)
    ec_before = piecewise.args[:index]

    if index < 0:
        index += len(piecewise.args)

    ec_after = piecewise.args[index + 1:]
    [*args] = ec_before + _ec + ec_after
    if not args[-1][1]:
        args[-1] = (args[-1][0], True)
    return piecewise.func(*args)


@apply
def apply(piecewise, index=None):
    return Equal(piecewise, flatten(piecewise, index))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,))
    A, B = Symbol(etype=dtype.real[k])
    f, g, h = Function(shape=(), real=True)
    Eq << apply(Piecewise((Piecewise((g(x), Element(x, B)), (h(x), True)), Element(x, A)), (f(x), True)))

    p = Symbol(Eq[0].lhs)
    Eq << p.this.definition

    Eq << Logic.OrAndS.of.BFn_Ite.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].args[0].apply(Logic.OrAndS.of.BFn_Ite)

    Eq << Eq[-1].this.find(And[Or]).apply(Logic.OrAndS.of.And_Or)

    Eq << Logic.BFn_Ite__Ite.of.And.ou.OrAndS.apply(Eq[-1], wrt=p)

    Eq << Eq[-1].this.lhs.apply(Logic.Ite.eq.Ite__IteOr)

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[1], Eq[-1])





if __name__ == '__main__':
    run()

# created on 2018-01-20
# updated on 2023-05-10
