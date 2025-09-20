from util import *



@apply
def apply(given):
    fn, *limits = given.of(All)
    return fn


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    S = Symbol(etype=dtype.real)
    e = Symbol(real=True)
    f = Function(shape=(), integer=True)
    Eq << apply(All[e:S](f(e) > 0))

    Eq << Logic.All.given.All_Or_Not.apply(Eq[0])

    Eq << Logic.Or.given.Cond.apply(Eq[-1], index=0)




if __name__ == '__main__':
    run()

# created on 2018-12-13
# updated on 2023-05-20

from . import subst
