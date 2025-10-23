from util import *


@apply
def apply(x):
    from Lemma.Discrete.K.eq.Add.definition import K
    assert x > 0
    return Unequal(K(x), 0)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Nat

    x = Symbol(real=True, positive=True, shape=(oo,))
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(x[:n])

    Eq << Discrete.K.gt.Zero.apply(x[:n])

    Eq << Nat.Ne.of.Gt.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-05
# updated on 2025-04-20
