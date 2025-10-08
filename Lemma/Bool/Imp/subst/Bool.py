from util import *



@apply
def apply(given, index=None, invert=False):
    p, q = given.of(Imply)
    if index is None:
        cond = p
    else:
        eqs = p.of(And)
        cond = eqs[index]

    if invert:
        old = cond.invert()
        new = S.false
    else:
        old = cond
        new = S.true

    q = q._subs(old, new)
    return Imply(p, q)


@prove
def prove(Eq):
    from Lemma import Bool
    x, y = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g = Function(real=True)

    Eq << apply(Imply(Equal(f(x), x + 1) & Element(x, A),
                           Equal(Piecewise((g(x), Equal(f(x), x + 1)), (g(y), True)), y)),
                           index=0)

    Eq << Iff(Imply(Equal(f(x), x + 1) & Element(x, A),
                                Equal(Piecewise((g(x), Equal(f(x), x + 1)), (g(y), True)), y)),

                     Imply(Equal(functions.Bool(Equal(f(x), x + 1)), 1) & Element(x, A),
                                Equal(Piecewise((g(x), Equal(functions.Bool(Equal(f(x), x + 1)), 1)), (g(y), True)), y)),

                     plausible=True)

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq[1].this.rhs.apply(Bool.IffImpSAndEq)

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)


if __name__ == '__main__':
    run()
# created on 2019-10-06
