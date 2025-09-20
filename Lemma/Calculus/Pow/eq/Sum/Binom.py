from util import *


@apply
def apply(self, n=None):
    x, r = self.of(Pow)
    x -= 1
    assert r.is_real
    if n is None:
        n = Symbol(integer=True)
        
    return Equal(self, Sum[n:oo](binomial(r, n) * x ** n))


@prove(proved=False)
def prove(Eq):
    x, r = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply((x + 1) ** r, n=n)

    
    


if __name__ == '__main__':
    run()

# created on 2020-10-20
# updated on 2021-11-25