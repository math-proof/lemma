from util import *


@apply
def apply(given, index=0):
    [*eqs] = given.of(And)

    del eqs[index]
    assert len(eqs) > 1

    if index < 0:
        index += len(eqs)

    if not index:
        index += 1

    first = eqs[:index]
    second = eqs[index:]

    first = And(*first)
    second = And(*second)

    return first, second


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    k = Symbol(integer=True, positive=True)
    a, b = Symbol(integer=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    f, g = Function(shape=(k,), real=True)
    Eq << apply(Unequal(x, y) & Equal(f(x), g(y)) & (a > b), index=0)

    Eq << Bool.And_And.of.And.apply(Eq[0], 1)

    Eq <<= Eq[1] & Eq[2]


if __name__ == '__main__':
    run()

# created on 2019-05-05
