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
    from Lemma import Algebra, Bool

    y, x = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    t, f, g = Function(integer=True)
    Eq << apply(Imply(Element(t(x), A), Equal(Piecewise((f(t(x), y), Element(t(x), A)), (g(x), True)), g(x))))

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Bool.BFn.of.BFnIte.Cond, swap=True)


if __name__ == '__main__':
    run()
# created on 2019-10-05
