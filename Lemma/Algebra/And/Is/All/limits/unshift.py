from util import *


@apply
def apply(self):
    [*eqs] = self.of(And)

    for i, eq in enumerate(eqs):
        if eq.is_ForAll:
            break
    else:
        return

    forall = eqs.pop(i)

    function, (i, a, b) = forall.of(All[Tuple])
    assert i.is_integer
    try:
        while eqs:
            j = eqs.index(function._subs(i, a - 1))
            del eqs[j]
            a -= 1
    except:
        return

    return All[i:a:b](function)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(domain=Range(n))

    x = Symbol(real=True, shape=(oo,))

    Eq << apply(And(All[i:a:n](x[i] > 0), x[a - 1] > 0, x[a - 2] > 0))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.All.given.And.All, cond={a - 2}), Eq[-1].this.lhs.apply(Bool.All.All.of.All, cond={a - 2})

    Eq <<= Eq[-2].this.rhs.apply(Algebra.All.given.And.All, cond={a - 1}), Eq[-1].this.lhs.find(All).apply(Bool.All.All.of.All, cond={a - 1})


if __name__ == '__main__':
    run()

# created on 2019-05-06
