from util import *


@apply
def apply(self, pivot=-1):
    args, *limits = self.of(Stack[Mul])
    first, second = std.array_split(args, pivot)
    first, second = Mul(*first), Mul(*second)

    first = Stack(first, *limits).simplify(squeeze=True)
    second = Stack(second, *limits).simplify(squeeze=True)

    function = Mul(first, second)
    max_len = max(len(first.shape), len(second.shape))
    if max_len < len(self.shape):
        rhs = Stack(function, *limits[:len(self.shape) - max_len])
    else:
        rhs = function

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a, b = Symbol(real=True, shape=(oo,))
    Eq << apply(Stack[j:n](a[j] * b[j]))

    _j = Symbol('j', domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], _j)




if __name__ == '__main__':
    run()

# updated on 2023-06-08
