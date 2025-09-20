from util import *


@apply
def apply(self):
    function, *limits = self.of(Sum)
    return Equal(self, Sum(function * Bool(self.limits_cond), *((x,) for x, *_ in limits)))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[x:A, y:B](f(x, y)))

    Eq << Eq[0].this.find(Bool).apply(Logic.BoolAnd.eq.MulBoolS)

    Eq << Sum[x](Eq[-1].rhs.expr).this.find(Bool).apply(Logic.Bool.eq.Ite)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum_Mul.eq.Mul_Sum)

    Eq << Algebra.EqSumS.of.Eq.apply(Eq[-1], (y,))

    Eq << Eq[1].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.expr.args[0].apply(Logic.Bool.eq.Ite)





if __name__ == '__main__':
    run()

# created on 2018-02-19
# updated on 2022-10-04
