from util import *


@apply
def apply(given):
    return piecewise_to_ou(given)


def piecewise_to_ou(given):
    cls = given.func
    piecewise, sym = given.args
    if sym.is_Piecewise:
        piecewise, sym = sym, piecewise
        func = lambda x, y: cls(y, x)
    else:
        func = cls

    piecewise = piecewise.of(Piecewise)

    univeralSet = S.BooleanTrue
    args = []

    for expr, cond in piecewise:
        condition = cond & univeralSet

        if not cond:
            invert = condition.invert()
            univeralSet &= invert

        eq = condition & func(expr, sym).simplify()
        args.append(eq)

    return Or(*args)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real[k], given=True)
    f, g, h = Function(shape=(k,), real=True)
    Eq << apply(Equal(p, Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True))))

    Eq << Eq[0].apply(Logic.AndOrS.of.Cond, cond=Element(x, A))

    Eq << Logic.And_And.of.And.apply(Eq[-1])

    Eq <<= Logic.Or_AndNot.of.Or.apply(Eq[-2], pivot=1), Logic.Or_AndNot.of.Or.apply(Eq[-1], pivot=1)

    Eq <<= Eq[-2].this.find(And).apply(Logic.BFn.of.BFnIte.Cond, invert=True, swap=True, ret=1), Eq[-1].this.find(And).apply(Logic.BFn.of.BFnIte.Cond, swap=True, ret=1)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Logic.OrAndS.of.And_Or.apply(Eq[-1])

    Eq << Eq[-1].this.find(Equal[Piecewise]).apply(Logic.OrAndS.of.BFn_Ite.binary)

    Eq << Eq[-1].this.find(And[Or]).apply(Logic.OrAndS.of.And_Or)





if __name__ == '__main__':
    run()

# created on 2018-01-07
# updated on 2023-05-17


from . import binary