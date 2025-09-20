from util import *


@apply
def apply(imply, wrt=None):
    B, A = imply.of(Subset)
    if wrt is None:
        wrt = imply.generate_var(**B.etype.dict)
    elif isinstance(wrt, str):
        wrt = imply.generate_var(**B.etype.dict, var=wrt)

    return All[wrt:B](Element(wrt, A))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    n = Symbol(complex=True, positive=True)
    A, B = Symbol(etype=dtype.complex[n], given=True)
    Eq << apply(Subset(B, A))

    Eq << Set.Subset.given.Eq_Empty.SDiff.apply(Eq[0])

    Eq << ~Eq[-1]

    Eq << Set.Any_In.of.SDiff.ne.Empty.apply(Eq[-1], simplify=False, wrt=Eq[1].variable)

    Eq << Logic.Any_And.of.Any.All.All_Imp.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-03-27
