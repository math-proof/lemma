from util import *


@apply
def apply(given, *, cond=None):
    assert cond.is_bool
    return Imply(cond, given), cond


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    p = Symbol(bool=True)
    f = Function(integer=True, shape=())
    Eq << apply(f(e) > 0, cond=p)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[2], Eq[1])




if __name__ == '__main__':
    run()
# created on 2023-04-18


