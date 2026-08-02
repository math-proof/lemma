from util import *



@apply
def apply(given, index):
    x, S = given.of(Element)
    a = given.generate_var(**x.type.dict)
    return Any[a:S](Equal(x[index], a[index]))


@prove
def prove(Eq):
    from Lemma import Set, Algebra
    n = Symbol(positive=True, integer=True)
    x = Symbol(integer=True, shape=(n,))
    i = Symbol(integer=True)
    S = Symbol(etype=dtype.integer[n])

    Eq << apply(Element(x, S), index=i)

    a = Eq[-1].variable

    Eq << Algebra.Any.given.Any.subst.apply(Eq[-1], a, x)

    Eq << Set.Any_In.given.Ne_Empty.apply(Eq[-1])

    Eq << Set.Ne_Empty.of.In.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2021-03-02
