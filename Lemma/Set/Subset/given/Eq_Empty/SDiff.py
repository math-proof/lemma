from util import *


@apply
def apply(imply):
    B, A = imply.of(Subset)
    return Equal(Complement(B, A), A.etype.emptySet)


@prove
def prove(Eq):
    from Lemma import Set
    A, B = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Subset(B, A))

    Eq << Set.Subset.SDiff.of.Eq_Empty.apply(Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-03-04
