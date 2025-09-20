from util import *


@apply
def apply(self):
    ((a, j), (i, S[j])), (S[j], S[0], k), (S[i], S[1], n) = self.of(Sum[Indexed * Pow])
    n -= 1
 
    return Equal(self, Stack[i:1:k + 1](n ** k) @ Inverse(Stack[j:k, i:k]((-1) ** (j - i) * Binomial(j + 1, i))) @ a[:k])


@prove(proved=False)
def prove(Eq):
    n, k = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    a = Symbol(real=True, shape=(oo,))
    Eq << apply(Sum[j:k, i:1:n + 1](a[j] * i ** j))

    Eq << Eq[-1].rhs.shape

    # https://baike.baidu.com/item/%E7%AD%89%E5%B7%AE%E6%95%B0%E5%88%97/1129192?fr=aladdin
    


if __name__ == '__main__':
    run()
# created on 2022-01-15
# updated on 2022-01-18
