from util import *


@apply
def apply(imply):
    limits = None
    eqs = []
    for exist in imply.of(Or):
        fn, *_limits = exist.of(Any)
        if limits is None:
            limits = _limits
        else:
            assert limits == _limits
        eqs.append(fn)

    return Any(Or(*eqs), *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)

    f, g = Function(integer=True)

    Eq << apply(Or(Any[x:A]((g(x) > 0)), Any[x:A](f(x) > 0)))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.rhs.apply(Bool.Any_Or.given.OrAnyS)

    Eq << Eq[-1].this.lhs.apply(Bool.OrAnyS.of.Any_Or)


if __name__ == '__main__':
    run()

# created on 2020-02-20
