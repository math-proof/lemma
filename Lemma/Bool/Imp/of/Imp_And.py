from util import *


@apply
def apply(given, index=0):
    fx, fy = given.of(Imply)
    eqs = fy.of(And)

    if isinstance(index, slice):
        eqs = eqs[index]
        return tuple(Imply(fx, eq) for eq in eqs)
    return Imply(fx, eqs[index])


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y = Symbol(integer=True)
    f, h, g = Function(integer=True)
    Eq << apply(Imply(Equal(h(x), h(y)), Equal(f(x), f(y)) & Equal(g(x), g(y))), index=0)

    Eq << Eq[0].this.rhs.apply(Bool.Cond.of.And, index=0)


if __name__ == '__main__':
    run()

# created on 2018-06-09
