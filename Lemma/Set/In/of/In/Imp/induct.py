from util import *



@apply
def apply(f0, suffice, n=None, start=0):
    start = sympify(start)
    f0.of(Element)

    fn, fn1 = suffice.of(Imply)
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, start) == f0
    assert n.domain.min() == start

    return fn


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool
    n = Symbol(integer=True, nonnegative=True)
    f = Symbol(integer=True, shape=(oo,))
    g = Symbol(etype=dtype.integer, shape=(oo,))

    Eq << apply(Element(f[0], g[0]), Imply(Element(f[n], g[n]), Element(f[n + 1], g[n + 1])), n=n)

    h = Symbol(Stack[n]((Element(f[n], g[n])).toNat))

    Eq << h[0].this.definition

    Eq << Set.Eq.Bool.In.of.In.apply(Eq[0])

    Eq << Eq[-1] + Eq[-2]

    Eq.equality = Eq[-1].this.apply(Algebra.EqAddS.Is.Eq)

    Eq.suffice = Imply(Equal(h[n], 1), Equal(h[n + 1], 1), plausible=True)

    Eq << Eq.suffice.this.lhs.lhs.definition

    Eq << Eq[-1].this.lhs.lhs.apply(Bool.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.lhs.definition

    Eq << Eq[-1].this.rhs.lhs.apply(Bool.Bool.eq.Ite)

    Eq << Bool.Cond.of.Cond.All_Imp.apply(Eq.equality, Eq.suffice, n=n)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.lhs.apply(Bool.Bool.eq.Ite)


if __name__ == '__main__':
    run()
# created on 2021-03-15
