from util import *



@apply
def apply(imply):
    function, *limits = imply.of(Any)
    assert all(len(limit) == 1 for limit in limits)
    return function


@prove
def prove(Eq):
    from Lemma import Algebra

    e = Symbol(real=True)
    f = Function(integer=True)
    Eq << apply(Any[e](f(e) > 0))

    Eq << Algebra.Any.of.Cond.apply(Eq[1], wrt=e)


if __name__ == '__main__':
    run()


# created on 2018-12-02

from . import subst
