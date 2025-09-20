from util import *



@apply
def apply(self):
    for i, union in enumerate(self.args):
        if isinstance(union, Cap):
            args = [*self.args]
            del args[i]
            this = self.func(*args)
            function = union.expr | this
            return Equal(self, union.func(function, *union.limits), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Set
    x = Symbol(etype=dtype.integer)
    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(etype=dtype.integer)
    Eq << apply(Cap[k:n](f(k)) | x)

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Set.In_Cap.given.All_In),\
    Eq[-1].this.lhs.apply(Set.All_In.of.In_Cap)

    Eq <<= Eq[-2].this.rhs.expr.apply(Set.In_Union.given.OrInS),\
    Eq[-1].this.lhs.expr.apply(Set.OrInS.of.In_Union)

    Eq <<= Eq[-2].this.lhs.apply(Set.OrInS.of.In_Union),\
    Eq[-1].this.rhs.apply(Set.In_Union.given.OrInS)

    Eq <<= Eq[-2].this.find(Element[Cap]).apply(Set.All_In.of.In_Cap),\
    Eq[-1].this.find(Element[Cap]).apply(Set.In_Cap.given.All_In)

if __name__ == '__main__':
    run()
# created on 2021-07-11
