from util import *


@apply
def apply(self):
    A = self.of(Determinant)
    n = A.shape[0]
    p = self.generate_var(shape=(n,), integer=True, var='p')
    i = self.generate_var(integer=True, var='i')
    j = self.generate_var(integer=True, var='j')

    return Equal(self, Sum[p:Equal(p[:n].cup_finiteset(), Range(n))]((-1) ** Sum[j:i, i:n](Bool(p[i] < p[j])) * Product[i:n](A[i, p[i]])))


@prove(provable=False)
def prove(Eq):
    n = Symbol(domain=Range(1, oo))
    A = Symbol(shape=(n, n), real=True)

    Eq << apply(Determinant(A))


if __name__ == '__main__':
    run()
# created on 2021-09-26
