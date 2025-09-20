from util import *

def extract(x, *ab, function=None):
    if not ab:
        if function is None:
            domain = x.universalSet
        else:
            domain = function.domain_defined(x)
    elif len(ab) == 1:
        domain = ab[0]
#         if domain.is_bool:
#             domain = x.domain_conditioned(domain)
    else:
        a, b = ab
        if b.is_set:
            domain = b & x.domain_conditioned(a)
        else:
            if x.is_integer:
                domain = Range(a, b)
            else:
                domain = Interval(a, b, left_open=True, right_open=True)
    return x, domain


@apply
def apply(given, old, new):
    cond, *limits, limit = given.of(All)
    S[old], domain = extract(*limit)
    if domain.is_set:
        assert domain.conditionally_contains(new)
    elif domain.is_bool:
        assert domain._subs(old, new)
    else:
        return

    if limits:
        cond = All(cond, *limits)

    return cond._subs(old, new)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(shape=(), integer=True)
    s = Symbol(etype=dtype.integer)
    Eq << apply(All[x:n + 1](Element(f(x), s)), x, n)

    Eq << Logic.All.All.of.All.apply(Eq[0], cond={n})




if __name__ == '__main__':
    run()

# created on 2018-12-18
# updated on 2023-05-03
