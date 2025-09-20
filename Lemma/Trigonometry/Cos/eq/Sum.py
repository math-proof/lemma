from util import *



@apply
def apply(self):
    x = self.of(Cos)
    n = self.generate_var(integer=True, var='n')
    return Equal(self, Sum[n:oo]((-1) ** n * x ** (2 * n) / factorial(2 * n)))


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(cos(x))

# https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F
if __name__ == '__main__':
    run()
# created on 2018-06-01
