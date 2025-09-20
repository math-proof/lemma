from util import *


@apply
def apply(self, var='k'):
    args, n = self.of(Pow[Add])
    size = len(args)
    i = self.generate_var(integer=True, shape=(oo,), var=var)
    indices = [i[t] for t in range(len(args))]
    from functools import reduce
    return Equal(self, Sum[i[:size]:Equal(sum(indices), n):CartesianSpace(Range(0, n + 1), len(indices))](
        Multinomial(n, *indices) * reduce(lambda x, y: x * y,
                                          (arg ** index for index, arg in zip(indices, args)))))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete

    x = Symbol(complex=True, shape=(3,))
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply((x[0] + x[1] + x[2]) ** n)

    i = Symbol(integer=True)
    Eq << Algebra.Pow.Sum.eq.Sum.apply(Sum[i:3](x[i]) ** n)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.eq.Add.doit)

    Eq << Eq[-1].this.find(ReducedSum).apply(Algebra.ReducedSum.eq.Add.doit)

    Eq << Eq[-1].this.find(Product).apply(Algebra.Prod.eq.Mul.doit)

    Eq << Eq[-1].this.find(Product).apply(Algebra.Prod.eq.Mul.doit)

    Eq << Eq[0].this.find(Multinomial).apply(Discrete.Choose.eq.Div.Factorial)


if __name__ == '__main__':
    run()
# created on 2023-08-20
