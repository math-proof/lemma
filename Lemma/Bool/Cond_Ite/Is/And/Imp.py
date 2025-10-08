from util import *


def piecewise_to_et(given, list=True):
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

        args.append(Imply(condition, func(expr, sym).simplify()))

    if list:
        return tuple(args)
    return And(*args)

@apply
def apply(self):
    return piecewise_to_et(self, False)



@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, p = Symbol(real=True, shape=(), given=True)
    A, B = Symbol(etype=dtype.real, given=True)
    f, g, h = Function(shape=(), real=True)
    Eq << apply(Equal(p, Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True))))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Bool.And.Imp.of.Cond_Ite)

    Eq <<= Eq[-1].this.rhs.apply(Bool.Cond_Ite.given.And.Imp)





if __name__ == '__main__':
    run()
# created on 2023-04-25
# updated on 2023-04-29
