from util import *


@apply
def apply(is_even, el):
    n = is_even.of(Equal[Expr % 2, 0])
    S[n], (a, b) = el.of(Element[Range])

    b -= 1

    return Element(n, imageset(n, 2 * n, Range((a + 1) // 2, b // 2 + 1)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    a, b, n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 0), Element(n, Range(a, b + 1)))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.In.of.Eq_even.In)

    Eq << Eq[-1].this.lhs.apply(Set.And.Eq_even.of.In)





if __name__ == '__main__':
    run()

# created on 2018-05-28
# updated on 2023-05-21
