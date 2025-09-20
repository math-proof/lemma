from util import *



# given: A in B
# => {A} subset B
@apply
def apply(given):
    e, s = given.of(Element)

    return Subset(e.set, s)


@prove
def prove(Eq):
    from Lemma import Set
    e = Symbol(integer=True)
    s = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, s, evaluate=False))

    Eq << Set.In.of.Subset.apply(Eq[1])

if __name__ == '__main__':
    run()

# created on 2020-07-27
del Cup
from . import Cup
