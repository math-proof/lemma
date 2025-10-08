from util import *


@apply
def apply(self):
    r, (p, q) = self.of(Imply[Imply])
    return Imply(r, Imply(p, q & r))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    n = Symbol(integer=True, nonnegative=True)
    A, B, C = Symbol(etype=dtype.integer)
    Eq << apply(Imply(Element(n, C), Imply(Element(n, A), Element(n, B))))

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.swap)

    Eq << Eq[-1].this.rhs.rhs.rhs.apply(Set.In_Inter.Is.And_In_Inter)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.swap)





if __name__ == '__main__':
    run()
# created on 2019-10-09
# updated on 2023-05-21
