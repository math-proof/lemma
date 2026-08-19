from util import *


@apply
def apply(self, b):
    expr, *limits, (x, *ac) = self.of(Integral)

    if ac:
        a, c = ac
    else:
        a = -oo
        c = oo

    return Equal(self, Integral[x:a:b](expr, *limits) + Integral[x:b:c](expr, *limits))


@prove
def prove(Eq):
    from Lemma import Real

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x:a:c](f(x)), b)

    Eq << Eq[0].this.rhs.apply(Real.Add.eq.Integral.concat)




if __name__ == '__main__':
    run()
# created on 2023-03-21
