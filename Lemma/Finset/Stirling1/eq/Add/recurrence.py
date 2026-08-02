from util import *


@apply
def apply(self):
    n, k = self.of(Stirling1)
    n -= 1
    k -= 1
    return Equal(self, Stirling1(n, k) + n * Stirling1(n, k + 1))


@prove(proved=False)
def prove(Eq):
    k, n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Stirling1(n + 1, k + 1))

    
    


if __name__ == '__main__':
    run()

# created on 2021-07-31
# updated on 2023-08-26
