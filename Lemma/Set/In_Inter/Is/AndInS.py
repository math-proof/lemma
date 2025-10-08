from util import *


@apply
def apply(given, index=-1):
    e, args = given.of(Element[Intersection])
    first = Intersection(*args[:index])
    second = Intersection(*args[index:])
    return And(Element(e, first), Element(e, second))


@prove
def prove(Eq):
    from Lemma import Set, Bool

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A & B))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.In.In.of.In_Inter), Eq[-1].this.lhs.apply(Set.In_Inter.of.In.In)




if __name__ == '__main__':
    run()
# created on 2022-01-01

