from util import *


@apply(simplify=False)
def apply(self, simplify=True):
    from Lemma.Set.OrInS.of.In_Union import split
    return split(self, simplify=simplify)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A | B))

    Eq <<= ~Eq[0] & Eq[1]

    Eq << Eq[-1].this.find(NotElement).apply(Set.AndNotSIn.of.NotIn_Union, simplify=None)

    Eq << Bool.OrAndS.of.And_Or.apply(Eq[-1])





if __name__ == '__main__':
    run()

# created on 2018-01-10
# updated on 2023-05-20

