from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(MatProduct)
    assert i.is_integer
    back = function._subs(i, b - 1)
#     b >= a => b + 1 >= a
    assert a <= b - 1
    return Equal(self, MatMul(MatProduct[i:a:b - 1](function), back), evaluate=False)


@prove(provable=False)
def prove(Eq):
    i = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(m, m))
    Eq << apply(MatProduct[i:n + 1](f(i)))




if __name__ == '__main__':
    run()
# created on 2020-08-29
