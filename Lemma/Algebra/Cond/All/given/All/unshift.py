from util import *


@apply
def apply(cond, all):
    fn, (k, a, b) = all.of(All)

    assert k.is_integer
    assert fn._subs(k, a - 1) == cond

    return All[k:a - 1:b](fn)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g = Function(integer=True)
    Eq << apply(g(a - 1) > 0, All[k:a:b](g(k) > 0))

    Eq << Bool.All.All.of.All.apply(Eq[-1], cond={a - 1})




if __name__ == '__main__':
    run()
# created on 2019-03-12
