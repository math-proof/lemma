from util import *


@apply
def apply(self):
    args, *limits = self.of(Variance[Add])
    size = len(args)

    if size == len(limits):
        i = 0
        occupied = [None] * size
        for v, *ab in limits:
            for i in range(i, i + size):
                i %= size
                if occupied[i]:
                    continue

                if args[i]._has(v):
                    occupied[i] = True
                    i += 1
                    break
            else :
                return
    else:
        assert not self.is_random

    sgm = 0
    for i in range(size):
        for j in range(size):
            if i == j:
                sgm += Variance(args[i])
            else:
                sgm += Covariance(args[i], args[j])

    return Equal(self, sgm)


@prove
def prove(Eq):
    from Lemma import Probability

    x = Symbol(real=True, shape=(oo,), random=True)
    Eq << apply(Variance(x[0] + x[1]))

    Eq << Eq[0].lhs.this.apply(Probability.Var.eq.Cov)

    Eq << Eq[-1].this.rhs.apply(Probability.Cov.Add.eq.Add.Cov, deep=True)




if __name__ == '__main__':
    run()
# created on 2023-04-19

