from util import *


@apply
def apply(self):
    expr, *limits_d = self.of(Derivative[Bool])
    return Equal(self, 0)


@prove
def prove(Eq):
    from Lemma import Real, Bool

    x = Symbol(real=True)
    p = Function(bool=True)
    Eq << apply(Derivative[x](functions.Bool(p(x))))

    Eq << Eq[0].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq[-1].this.lhs.apply(Real.Grad.eq.Ite)




if __name__ == '__main__':
    run()
# created on 2023-06-21
