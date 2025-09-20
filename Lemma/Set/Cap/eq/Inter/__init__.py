from util import *


@apply
def apply(self):
    fx, *limits = self.of(Cap)
    args = fx.of(Intersection)

    return Equal(self, Intersection(*(Cap(arg, *limits) for arg in args)))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cap[x:A, y:B](f(x, y) & g(x, y)))

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0], wrt=y)

    Eq <<= Eq[-2].this.rhs.apply(Set.In_Inter.given.In.In, simplify=False), \
    Eq[-1].this.lhs.apply(Set.In.In.of.In_Inter, simplify=False)

    Eq <<= Eq[-2].this.rhs.args[0].apply(Set.In_Cap.given.All_In), \
    Eq[-1].this.lhs.args[0].apply(Set.All_In.of.In_Cap)

    Eq <<= Eq[-2].this.rhs.args[0].apply(Set.In_Cap.given.All_In), \
    Eq[-1].this.lhs.args[0].apply(Set.All_In.of.In_Cap)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.All.All.given.All.And), \
    Eq[-1].this.lhs.apply(Logic.All_And.of.All.All)

    Eq <<= Eq[-2].this.lhs.apply(Set.All_In.of.In_Cap), \
    Eq[-1].this.rhs.apply(Set.In_Cap.given.All_In)


if __name__ == '__main__':
    run()


# created on 2021-01-31
from . import doit
from . import single_variable
