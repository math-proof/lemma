from util import *


@apply
def apply(self):
    p, q = self.of(Add)
    p = p.of(Bool)
    q = q.of(Bool)

    return Equal(self, Bool(p | q) + Bool(p & q))


@prove
def prove(Eq):
    from Lemma import Set, Bool

    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    Eq << apply(functions.Bool(Element(x, A)) + functions.Bool(Element(x, B)))

    Eq << Eq[-1].this.rhs.args[1].arg.apply(Set.In_Union.Is.OrInS)

    Eq << Eq[-1].this.find(functions.Bool[Or]).apply(Bool.BoolOr.eq.SubAddBoolS)




if __name__ == '__main__':
    run()

# created on 2018-08-03
# updated on 2023-04-18
