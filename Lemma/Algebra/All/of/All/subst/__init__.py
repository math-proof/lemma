from util import *


@apply
def apply(given, old, new):
    cond, *limits = given.of(All)
    for i, (x, *args) in enumerate(limits):
        if x == old:
            break
    else:
        return
    limits_prior = limits[:i]
    limit = limits[i]
    limits_post = limits[i + 1:]
    from Lemma.Algebra.Cond.of.All.subst import extract
    S[old], domain = extract(*limit)
    if domain.is_set:
        assert domain.conditionally_contains(new)
    elif domain.is_bool:
        assert domain._subs(old, new)
    else:
        return

    if limits_prior:
        cond = All(cond, *limits_prior)

    cond = cond._subs(old, new)
    assert limits_post
    return All(cond, *limits_post)


@prove
def prove(Eq):
    from Lemma import Algebra

    i = Symbol(integer=True)
    x = Symbol(real=True)
    a = Symbol(real=True, shape=(oo,))
    c = Function(bool=True)
    f = Function(real=True)
    s = Symbol(etype=dtype.integer)
    Eq << apply(All[x:c(x)](Element(f(x), s)), x, a[i])



if __name__ == '__main__':
    run()
# created on 2024-06-28


from . import inner
