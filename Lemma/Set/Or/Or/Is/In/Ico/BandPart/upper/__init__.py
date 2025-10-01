from util import *


@apply
def apply(ou, ou_et):
    ((j, i), (S[0], u)), ((S[i], (n, S[u])), (S[j], S[i])) = ou_et.of(Element[Expr - Expr, Range] | (Symbol >= Expr - Expr) & GreaterEqual)
    (S[j], S[i]), (S[i], S[n - u]) = ou.of(GreaterEqual | Less)

    assert i in Range(n) and j in Range(n)
    return Element(j - i, Range(0, u))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    n, u = Symbol(domain=Range(2, oo), given=True)
    i, j = Symbol(domain=Range(n), given=True)
    Eq << apply(And(j >= i, i >= n - u) | Element(j - i, Range(u)), Or(j >= i, i < n - u))

    Eq << Eq[0].this.find(Or[2]).apply(Algebra.Or.invert, 0)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotIn_Ico.Is.Or)

    Eq << Eq[-1].this.find(And, And, Symbol >= Symbol) - i

    Eq << Eq[-1].this.find(Symbol >= Symbol) - i

    Eq << Eq[-1].this.find(Or[~And]).apply(Algebra.And.distribute, 1)

    Eq << Eq[-1].this.find(Add >= Symbol).apply(Algebra.Ge.transport, lhs=0)

    Eq << -Eq[-1].this.find(-Symbol >= Add)

    Eq << Eq[-1].this.lhs.apply(Algebra.And.invert, 0)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotIn_Ico.Is.Or)





if __name__ == '__main__':
    run()
# created on 2022-01-02


# updated on 2023-05-21
del Min
from . import Min
from . import offset
