from util import *


@apply
def apply(self, deep=False):
    lhs, rhs = self.of(Covariance)
    if lhs.is_Add:
        if rhs.is_Add and deep:
            sgm = []
            for a in lhs.args:
                var, cov = std.array_split(rhs.args, lambda b: a == b)
                sgm += [Variance(a)] * len(var)
                sgm += [Covariance(a, b) for b in cov]
            rhs = Add(*sgm)
        else:
            rhs = Add(*(Covariance(arg, rhs) for arg in lhs.args))
    elif rhs.is_Add:
        rhs = Add(*(Covariance(lhs, arg) for arg in rhs.args))
    else:
        return
    return Equal(self, rhs)


@prove
def prove(Eq):
    from Lemma import Probability, Algebra

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Covariance(x, y + z))

    Eq << Eq[0].this.lhs.apply(Probability.Cov.eq.Sub.Expect)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Expectation[Add]).apply(Probability.Expect.eq.Add)

    Eq << Eq[-1].this.find(Expectation[Add]).apply(Probability.Expect.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Covariance).apply(Probability.Cov.eq.Sub.Expect)

    Eq << Eq[-1].this.find(Covariance).apply(Probability.Cov.eq.Sub.Expect)




if __name__ == '__main__':
    run()
# created on 2023-04-19
