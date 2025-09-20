from util import *


@apply
def apply(given, invert=False):
    eq, f = given.of(Imply)
    if invert:
        old = eq.invert()
        new = S.false
    else:
        old = eq
        new = S.true

    return Imply(eq, f._subs(old, new))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    y, x = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    t, f, g = Function(integer=True)
    Eq << apply(Imply(Element(t(x), A), Equal(Piecewise((f(t(x), y), Element(t(x), A)), (g(x), True)), g(x))))

    Eq << Logic.Imp.given.Imp.And.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Logic.Cond.BFnIte.given.And_BFn)


if __name__ == '__main__':
    run()
# created on 2018-06-14
