from util import *


@apply
def apply(given, *, cond=None):
    assert cond.is_bool
    return Imply(cond, given), Imply(cond.invert(), given)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    e = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq <<= Eq[-2].apply(Logic.Imp.given.Or_Not), Eq[-1].apply(Logic.Imp.given.Or_Not)

    Eq <<= Logic.Or.given.Cond.apply(Eq[-2], index=0), Logic.Or.given.Cond.apply(Eq[-1], index=1)




if __name__ == '__main__':
    run()

# created on 2018-08-13
# updated on 2023-05-20
