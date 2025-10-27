from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Any)
    return Any[i](expr._subs(i, -i))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Int

    i, a, b, c = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i](f(i) >= 0))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Int.Any_UnaryFnNeg.of.Any)

    Eq << Eq[-1].this.lhs.apply(Int.Any_UnaryFnNeg.of.Any)


if __name__ == '__main__':
    run()
# created on 2018-07-10
