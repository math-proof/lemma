from util import *



@apply
def apply(given, wrt=None):
    fn, fn1 = given.of(Imply)
    if wrt is None:
        wrt = fn.wrt
    assert wrt.is_given is None
    return All[wrt:fn](fn1)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    n = Symbol(integer=True)

    A = Symbol(etype=dtype.integer)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Imply(Element(n, A), Equal(f[n], g[n])), wrt=n)

    Eq.suffice, Eq.necessary = Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq.suffice.this.lhs.apply(Bool.Or.of.ImpNot)

    Eq << Eq[-1].this.lhs.apply(Bool.All.of.All_OrNot, pivot=1, wrt=n)

    Eq << Eq.necessary.this.rhs.apply(Bool.Imp.given.Or_Not)

    Eq << Eq[-1].this.lhs.apply(Bool.Or_Not.of.All)


if __name__ == '__main__':
    run()
# created on 2018-09-18
