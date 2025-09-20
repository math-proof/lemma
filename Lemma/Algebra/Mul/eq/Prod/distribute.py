from util import *


@apply
def apply(self):
    (a, n), (fk, (k, i, S[n + i])) = self.of(Pow * Product)
    return Equal(self, Product[k:i:n + i](fk * a))


@prove
def prove(Eq):
    k, n = Symbol(integer=True)
    f = Function(real=True)
    a = Symbol(real=True)
    Eq << apply(a ** n * Product[k:n](f(k)))

    Eq << Eq[0].this.rhs.simplify()

    


if __name__ == '__main__':
    run()
# created on 2023-08-20
