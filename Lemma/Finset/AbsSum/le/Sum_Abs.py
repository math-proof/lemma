from util import *


@apply
def apply(self):
    expr, *limits = self.of(Sum)
    return Abs(self) <= Sum(Abs(expr), *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Int, Finset

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[k:n](f(k)))

    Eq << Finset.Sum.le.Sum_Abs.apply(Eq[0].lhs.find(Sum))

    @Function
    def g(x):
        return -f(x)
    Eq << Finset.Sum.le.Sum_Abs.apply(Eq[0].lhs.find(Sum)._subs(f(k), g(k)))

    Eq << Eq[-1].this.find(g).defun()

    Eq << -Eq[-1].this.find(g).defun()

    Eq << Int.LeAbs.of.LeNeg.Le.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-15
