from util import *



@apply
def apply(given, index=None, reverse=False):
    p, q = given.of(Imply)
    if index is None:
        if p.is_Equal:
            old, new = p.args
        else:
            eqs = p.of(And)
            for eq in eqs:
                if eq.is_Equal:
                    old, new = eq.args
                    break
    else:
        eqs = p.of(And)
        old, new = eqs[index].of(Equal)

    if reverse:
        old, new = new, old
    q = q._subs(old, new)
    return Imply(p, q)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x, y = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g = Function(real=True)

    Eq << apply(Imply(Equal(f(x), x + 1) & Element(x, A), Equal(g(f(x)), y)))

    Eq.suffice, Eq.necessary = Bool.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq.suffice.this.lhs.apply(Bool.Imp_And.of.ImpAnd, index=0)

    Eq << Eq[-1].this.lhs.rhs.apply(Bool.Cond.of.Eq.Cond.subst)

    Eq << Eq.necessary.this.lhs.apply(Bool.Imp_And.of.ImpAnd, index=0)

    Eq << Eq[-1].this.lhs.rhs.apply(Bool.Cond.of.Eq.Cond.subst, reverse=True)


if __name__ == '__main__':
    run()

# created on 2018-02-06
