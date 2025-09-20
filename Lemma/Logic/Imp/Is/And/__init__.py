from util import *


@apply
def apply(self):
    p, q = self.of(boolalg.Imply)

    return And(*(p >> eq for eq in q.of(And)))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y = Symbol(integer=True)
    f, g, h = Function(integer=True)
    Eq << apply((x > y) >> ((f(x) > g(y)) & (h(x) > g(y))))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Logic.And.Imp.of.Imp)

    Eq << Eq[-1].this.rhs.apply(Logic.Imp_And.given.Imp.Imp)


if __name__ == '__main__':
    run()
# created on 2019-10-07
from . import Imp
