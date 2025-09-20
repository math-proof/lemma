from util import *


@apply
def apply(cond, forall):
    fn, (k, a, b) = forall.of(All[Tuple])

    assert k.is_integer
    assert fn._subs(k, b) == cond

    return All[k:a:b + 1](fn)


@prove
def prove(Eq):
    from Lemma import Algebra

    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g = Function(integer=True)
    Eq << apply((g(b) > 0), All[k:a:b](g(k) > 0))

    Eq << Algebra.All.given.And.All.apply(Eq[-1], cond={b})


if __name__ == '__main__':
    run()

# created on 2019-03-12
