from util import *



# given: A in B
# => A | B = B
@apply
def apply(contains, forall):
    function, *limits = forall.of(All)
    b, A = contains.of(Element)

    index = -1
    for i, (x, *domain) in enumerate(limits):
        if len(domain) == 1:
            if domain[0] == A:
                index = i
                break

    assert index >= 0

    function = function._subs(x, b) if x != b else function
    limits = [*forall.limits]
    del limits[index]
    if limits:
        return All(function, *limits)

    return function


@prove
def prove(Eq):
    from Lemma import Algebra, Logic, Bool
    n = Symbol(complex=True, positive=True)
    A = Symbol(etype=dtype.complex[n])
    a, b = Symbol(complex=True, shape=(n,))

    f = Function(complex=True, shape=())

    assert f.is_complex
    assert f.shape == ()

    Eq << apply(Element(b, A), All[a:A](Equal(f(a), 1)))

    Eq << Bool.Or_NotIn.of.All.apply(Eq[1], a, b)

    Eq <<= Eq[-1] & Eq[0]

    Eq << Bool.And_And.of.And.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-02-24
