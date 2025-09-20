from util import *


@apply
def apply(ou, ou_et):
    ((j, i), ((l, n), S[0])), ((S[j], S[i]), (S[i], S[Min(n, l) - 1])) = ou_et.of(Element[Expr - Expr, Range[1 - Min]] | Less & Less)
    (S[i], S[Min(n, l) - 1]), (S[j], S[i]) = ou.of(GreaterEqual | Less)

    assert i in Range(n) and j in Range(n)
    return Element(j - i, Range(-l + 1, 0))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    n, l = Symbol(domain=Range(2, oo), given=True)
    i, j = Symbol(domain=Range(n), given=True)
    Eq << apply(And(j < i, i < Min(n, l) - 1) | Element(j - i, Range(1 - Min(n, l), 0)), Or(j < i, i >= Min(n, l) - 1))

    Eq << Eq[0].this.find(Or[2]).apply(Algebra.Or.invert, 0)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotIn_Range.Is.Or)

    Eq << Eq[-1].this.find(And, And, Symbol < Symbol) - i

    Eq << Eq[-1].this.find(Symbol < Symbol) - i

    Eq << Eq[-1].this.find(Or[~And]).apply(Algebra.And.distribute, 1)

    Eq << Eq[-1].this.find(Add < Add).apply(Algebra.Lt.transport, 0)

    Eq << -Eq[-1].this.find(-Symbol < Add)

    Eq << Eq[-1].this.lhs.apply(Algebra.And.invert, 0)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotIn_Range.Is.Or)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Range.Is.And)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Range.Is.And)

    Eq << Eq[-1].this.find(GreaterEqual[1 - Min]) - 1

    Eq << -Eq[-1].this.find(GreaterEqual[-Min])

    Eq << Eq[-1].this.find(LessEqual[Min]).apply(Algebra.Le_Min.Is.And.Le)

    Eq << Eq[-1].this.find(LessEqual) - 1

    Eq << -Eq[-1].this.find(LessEqual)





if __name__ == '__main__':
    run()
# created on 2022-01-02

# updated on 2023-05-21
