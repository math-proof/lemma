from util import *


@apply
def apply(given, n):
    from Lemma.Discrete.Alpha.gt.Zero import alpha
    (x, j), S[j] = given.of(All[Indexed > 0, Tuple[1, oo]])
    assert n > 0
    return Less(alpha(x[:2 * n - 1]), alpha(x[:2 * n + 1]))


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    Eq << apply(All[i:1:oo](x[i] > 0), n)


if __name__ == '__main__':
    run()

# created on 2021-08-13
