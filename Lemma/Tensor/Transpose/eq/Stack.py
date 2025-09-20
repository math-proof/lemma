from util import *


@apply
def apply(self):
    axis = self.axis
    f, *limits = self.of(Transpose[axis][Stack])
    variables = {var for var, *ab in limits}
    j = self.generate_var(variables, integer=True)

    t, k = axis
    assert k >= len(limits)
    if axis == self.default_axis:
        [(i, S[0], m)] = limits
        n, = f.shape
        rhs = Stack[i:m, j:n](f[j]).simplify()
    else:
        index = -axis - 1
        raise NotImplementedError

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    i, j = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, shape=(oo,))
    h = Symbol(real=True, shape=(oo, n, n))
    Eq << apply(Stack[i:m](h[j, d[i]]).T)

    i = Symbol(domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], i)




if __name__ == '__main__':
    run()
# created on 2022-01-11
