from util import *


@apply
def apply(self):
    from Lemma.Discrete.Sigma.eq.Add.recurrent import sigma
    assert self.is_sigma
    x, (k,) = self.args
    n = x.shape[0]
    assert k >= 2
    n -= 1
    return Equal(self, x[n] * sigma[k - 1](x[:n]) + sigma[k](x[:n]))




@prove(proved=False)
def prove(Eq):
    from Lemma import Set, Algebra
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(oo,))
    k = Symbol(domain=Range(2, n + 1))
    from Lemma.Discrete.Sigma.eq.Add.recurrent import sigma

    Eq << apply(sigma[k](x[:n + 1]))

    Eq << Eq[-1].this.find(sigma).defun()

    Eq << Eq[-1].this.find(sigma).defun()

    Eq << Eq[-1].this.find(sigma).defun()

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.split, cond=CartesianSpace(Range(n), k))

    Eq << Eq[-1].this.find(Complement).apply(Set.SDiff.eq.Conditionset)


if __name__ == '__main__':
    run()

# created on 2020-11-18
