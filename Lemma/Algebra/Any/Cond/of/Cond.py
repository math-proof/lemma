from util import *


@apply
def apply(given, *limits):
    print('axiom must be employed at the top level!', __file__)
    for x, *ab in limits:
        assert given._has(x)
        if len(ab) == 1:
            domain = ab[0]
            if domain.is_set:
                assert domain in given.domain_defined(x)
            else:
                return
        else:
            return

    return Any(given, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    e = Symbol(integer=True)
    A = Symbol(etype=dtype.integer, empty=False)
    f = Function(integer=True)
    Eq << apply(f(e) > 0, (e, A))

    Eq << Logic.AllIn.of.All.apply(Eq[0], (e, A))

    Eq << Algebra.Any.of.All.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-03-17
