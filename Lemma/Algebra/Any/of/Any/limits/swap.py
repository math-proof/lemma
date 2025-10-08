from util import *



@apply
def apply(self):
    function, *limits = self.of(Any)
    assert len(limits) == 2
    limit0, limit1 = limits

    x, *domain_x = limit0
    y, *domain_y = limit1

    for s in domain_x:
        assert not s._has(y)

    limits = limit1, limit0
    return Any(function, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x, y = Symbol(integer=True)
    A = Symbol(etype=dtype.integer, given=True)
    f, g = Function(integer=True)

    Eq << apply(Any[x:A, y:f(y) > 0](g(x, y) > 0))

    Eq << ~Eq[-1]

    Eq <<= Bool.Any_And.of.Any.All.All_Imp.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

# created on 2019-02-15
