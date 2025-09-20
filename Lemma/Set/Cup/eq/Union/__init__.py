from util import *

@apply
def apply(self):
    fx, *limits = self.of(Cup)
    args = fx.of(Union)

    return Equal(self, Union(*(Cup(arg, *limits) for arg in args)))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cup[x:A, y:B](f(x, y) | g(x, y)))

    # Eq << apply(Cup[x:A](f(x) | g(x)))
    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0], wrt=y)

    Eq <<= Eq[-2].this.rhs.apply(Set.In_Union.given.OrInS, simplify=False), \
    Eq[-1].this.lhs.apply(Set.OrInS.of.In_Union, simplify=False)

    Eq <<= Eq[-2].this.rhs.args[0].apply(Set.In_Cup.given.Any_In), \
    Eq[-1].this.lhs.args[0].apply(Set.Any_In.of.In_Cup)

    Eq <<= Eq[-2].this.rhs.args[0].apply(Set.In_Cup.given.Any_In), \
    Eq[-1].this.lhs.args[0].apply(Set.Any_In.of.In_Cup)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Or.given.Any.Or), \
    Eq[-1].this.lhs.apply(Algebra.Any.Or.of.Or)

    Eq <<= Eq[-2].this.rhs.expr.apply(Set.Or.given.In), \
    Eq[-1].this.lhs.expr.apply(Set.In.of.Or)

    Eq <<= Eq[-2].this.lhs.apply(Set.Any_In.of.In_Cup), \
    Eq[-1].this.rhs.apply(Set.In_Cup.given.Any_In)


if __name__ == '__main__':
    run()

# created on 2021-02-10

from . import doit
