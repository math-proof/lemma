from util import *



@apply
def apply(given, t):
    e, finiteset = given.of(Element)

    args = finiteset.of(FiniteSet)

    finiteset = finiteset.func(*(arg + t for arg in args))

    return Element(e + t, finiteset)


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(integer=True)
    a, b, t = Symbol(real=True)
    Eq << apply(Element(x, {a, b}), t)

    Eq << Set.OrEqS.of.In_Finset.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.args[0] + t

    Eq << Eq[-1].this.args[0] + t

    Eq << Set.In.Finset.of.Or_Eq.apply(Eq[-1])




if __name__ == '__main__':
    run()

# created on 2021-03-04
# updated on 2023-05-13
