from util import *


@apply
def apply(self):
    (cond, expr), (x,) = self.of(Integral[Mul[Bool]])
    domain = cond.domain_conditioned(x)
    a, b = domain.of(Interval)
    return Equal(self, Integral[x:a:b](expr), evaluate=False)


@prove(proved=False)
def prove(Eq):
    from Lemma import Calculus

    x, a = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x](f(x) * Bool(x <= a)))

    Eq << Eq[0].lhs.this.apply(Calculus.Integral.eq.Add.split, a)

    Eq << Eq[-1].this.rhs.args[0]().find(LessEqual).simplify()

    ε = Symbol(positive=True)
    Eq << Eq[-1].rhs.args[0].this.apply(Calculus.Integral.eq.Add.split, a + ε)

    Eq << Eq[-1].this.rhs.args[1]().find(LessEqual).simplify()





if __name__ == '__main__':
    run()
# created on 2021-07-24
# updated on 2023-04-10
