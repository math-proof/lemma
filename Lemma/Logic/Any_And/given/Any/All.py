from util import *


@apply
def apply(imply, index=-1):
    [*eqs], *limits = imply.of(Any[And])
    cond = eqs[index]
    del eqs[index]

    return cond, Any(And(*eqs), *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g = Function(integer=True)
    Eq << apply(Any[x:A]((g(x) > 0) & (f(x) > 0)))

    Eq << Logic.Any_And.of.Any.All.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

# created on 2018-12-03


