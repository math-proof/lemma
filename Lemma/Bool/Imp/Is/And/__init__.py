from util import *


@apply
def apply(self):
    p, q = self.of(boolalg.Imply)

    return And(*(p >> eq for eq in q.of(And)))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y = Symbol(integer=True)
    f, g, h = Function(integer=True)
    Eq << apply((x > y) >> ((f(x) > g(y)) & (h(x) > g(y))))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Bool.And.Imp.of.Imp)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp_And.given.Imp.Imp)


if __name__ == '__main__':
    run()
# created on 2019-10-07
from . import Imp
