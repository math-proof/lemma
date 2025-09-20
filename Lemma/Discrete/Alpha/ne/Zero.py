from util import *


@apply
def apply(x):
    from Lemma.Discrete.Alpha.gt.Zero import alpha
    return Unequal(alpha(x), 0)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra

    x = Symbol(integer=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    Eq << apply(x[:n])

    Eq << Discrete.Alpha.gt.Zero.apply(x, n)

    Eq << Eq[-1].apply(Algebra.Ne.of.Gt)

    


if __name__ == '__main__':
    run()

# created on 2020-09-18
# updated on 2025-04-20
