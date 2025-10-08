from util import *


@apply
def apply(given, index=None):
    x, intersection = given.of(Element)

    ss = intersection.of(Intersection)
    if index is None:
        et = [Element(x, s) for s in ss]
    else:
        ss = ss[index]
        if isinstance(index, slice):
            et = [Element(x, s) for s in ss]
            et.append(given)
        else:
            et = [Element(x, ss), given]
    return And(*et)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool
    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)

    Eq << apply(Element(x, A & B), index=0)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Set.In.of.In_Inter)


if __name__ == '__main__':
    run()

# created on 2019-10-08
