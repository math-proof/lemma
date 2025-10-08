from util import *



@apply
def apply(given):
    p, q = given.of(Given)
    return p | q.invert()


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    Eq << apply(Given(x > y, f(x) > g(y)))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Bool.Or_Not.of.Imp)

    Eq << Eq[-1].this.rhs.apply(Bool.ImpNot.given.Or)

if __name__ == '__main__':
    run()
# created on 2019-03-02
