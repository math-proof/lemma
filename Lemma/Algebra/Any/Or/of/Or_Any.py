from util import *


@apply
def apply(imply):
    eqs = imply.of(Or)
    limits = None
    conds = []
    for eq in eqs:
        cond, *_limits = eq.of(Any)
        if limits is None:
            limits = _limits
        else:
            assert limits == _limits
        conds.append(cond)

    return Any(Or(*conds), *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g = Function(bool=True)
    Eq << apply(Or(Any[x:A](g(x)), Any[x:A](f(x))))

    Eq << Logic.Any_Or.given.OrAnyS.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-07-01
