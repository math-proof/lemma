from util import *


@apply
def apply(imply):
    exists = imply.of(Or)
    limits = None
    eqs = []
    for exist in exists:
        fn, *_limits = exist.of(Any)
        if limits is None:
            limits = _limits
        else:
            assert limits == _limits
        eqs.append(fn)

    return Any(Or(*eqs), *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)

    f, g = Function(integer=True)

    Eq << apply(Or(Any[x:A]((g(x) > 0)), Any[x:A](f(x) > 0)))

    Eq << Logic.OrAnyS.of.Any_Or.apply(Eq[1])


if __name__ == '__main__':
    run()

# created on 2020-02-17
