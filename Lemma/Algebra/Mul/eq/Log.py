from util import *


@apply
def apply(self):
    *t, x = self.of(Expr * Log)
    t = Mul(*t)
    rhs = log(x ** t)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic, Real

    t = Symbol(real=True)
    x = Symbol(real=True, positive=True)
    Eq << apply(t * log(x))

    Eq << Real.Eq.given.EqExpS.apply(Eq[0])

    y = Symbol(log(x))
    Eq << y.this.definition

    Eq <<= Eq[-1] * t, Logic.EqUFnS.of.Eq.apply(Eq[-1], exp)

    Eq <<= Logic.EqUFnS.of.Eq.apply(Eq[-2], exp), Algebra.EqPowS.of.Eq.apply(Eq[-1], exp=t)
    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-01-29
