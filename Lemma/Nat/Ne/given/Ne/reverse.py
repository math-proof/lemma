from util import *


@apply
def apply(ne):
    a, b = ne.of(Unequal)
    return Unequal(b, a)


@prove
def prove(Eq):
    from Lemma import Nat

    b, a = Symbol(real=True, given=True)
    Eq << apply(Unequal(a, b))

    Eq << Nat.Ne.of.Ne.reverse.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2020-02-05
