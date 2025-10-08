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
            j = eqs.index(function._subs(i, b))
            del eqs[j]
            b += 1
    except:
        return

    return All[i:a:b](function)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    x = Symbol(real=True, shape=(oo,))

    Eq << apply(And(All[i:n](x[i] > 0), x[n] > 0, x[n + 1] > 0))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.All.given.And.All, cond={n + 1}), Eq[-1].this.lhs.apply(Bool.All.All.of.All, cond={n + 1})

    Eq <<= Eq[-2].this.rhs.apply(Algebra.All.given.And.All, cond={n}), Eq[-1].this.lhs.args[1].apply(Bool.All.All.of.All, cond={n})


if __name__ == '__main__':
    run()

# created on 2019-05-06
