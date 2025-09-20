from util import *


def new(p, q, simplify=True):
    if simplify:
        if isinstance(q, Imply):
            _p, q = q.args
            p &= _p
        cond = Imply(p, q)
        cond = cond.simplify()
    else:
        cond = Imply(p, q)
    return cond

@apply
def apply(given, index=-1, *, simplify=True):
    fx, fy = given.of(Imply)
    eqs = fy.of(And)


    if index is not None:
        first = eqs[:index]
        second = eqs[index:]

        first = And(*(new(fx, eq, simplify) for eq in first))
        second = And(*(new(fx, eq, simplify) for eq in second))
        return first, second

    return tuple(new(fx, eq, simplify) for eq in eqs)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, y = Symbol(integer=True)
    f, h, g = Function(integer=True)
    Eq << apply(Imply(Equal(h(x), h(y)), Equal(f(x), f(y)) & Equal(g(x), g(y))))

    Eq << Eq[0].this.rhs.apply(Logic.Cond.of.And, index=0)

    Eq << Eq[0].this.rhs.apply(Logic.Cond.of.And, index=1)


if __name__ == '__main__':
    run()
# created on 2018-08-16
from . import split
