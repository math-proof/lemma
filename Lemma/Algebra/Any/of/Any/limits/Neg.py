from util import *


@apply
def apply(self):
    expr, (i, *ab) = self.of(Any)
    from Lemma.Algebra.All.of.All.limits.Neg import negate
    return Any(expr._subs(i, -i), negate(i, *ab))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool, Int

    i, a, b = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i:a:b](f(i) >= 0))

    Eq << Bool.Any_And.of.AnySetOf_AnySetOf.apply(Eq[0], simplify=False)

    Eq << Int.Any_UFnNeg.of.Any.apply(Eq[-1])

    Eq << Eq[-1].this.find(Element).apply(Set.Neg.In.Icc.of.In_Icc)


if __name__ == '__main__':
    run()

# created on 2019-02-13


