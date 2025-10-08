from util import *


@apply
def apply(self):
    A, (p, q) = self.of(Imply[Basic, Imply])
    return Imply(p, Imply(A, q))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y, z = Symbol(real=True)
    A, B, C = Symbol(etype=dtype.real)
    Eq << apply(Imply(Element(x, A), Imply(Element(y, B), Element(z, C))))

    Eq << Eq[-1].this.lhs.apply(Bool.Imp.flatten)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.flatten)




if __name__ == '__main__':
    run()
# created on 2019-10-06
