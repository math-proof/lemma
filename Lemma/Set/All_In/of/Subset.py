from util import *




@apply
def apply(given, wrt=None):
    B, A = given.of(Subset)

    if wrt is None:
        x = B.element_symbol()
    else:
        x = wrt

    return All[x:B](Element(x, A))


@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(complex=True, positive=True)
    A, B = Symbol(etype=dtype.complex[n])

    Eq << apply(Subset(B, A))

    x = Eq[1].variable
    Eq << All[x:B](Element(x, B), plausible=True)

    Eq << Eq[-1].simplify()

    Eq << Eq[-1].this.expr.apply(Set.In.of.In.Subset, Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-03-30
