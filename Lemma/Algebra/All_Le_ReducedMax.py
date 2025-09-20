from util import *


@apply
def apply(self, var=None):
    expr = self.of(ReducedMax)
    if var is None:
        i = self.generate_var(integer=True)
    else:
        i = var
    return All[i:expr.shape[-1]](LessEqual(expr[i], self))


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(ReducedMax(x))

    i = Eq[0].variable
    Eq << Algebra.All_Le_Maxima.apply(Maxima[i:n](x[i]))

    Eq << Eq[0].this.expr.rhs.apply(Algebra.ReducedMax.eq.Maxima, var=i)




if __name__ == '__main__':
    run()
# created on 2023-10-04
