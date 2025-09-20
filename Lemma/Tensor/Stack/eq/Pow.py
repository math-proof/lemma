from util import *


@apply
def apply(self):
    p, *limits = self.of(Stack)
    if p.is_Mul:
        one, p = p.args
        assert one.is_Ones
        base, exponent = p.of(Pow)
        base *= one
    else:
        base, exponent = p.of(Pow)
    assert not exponent.shape
    variables = [v for v, *_ in limits]
    if exponent.has(*variables):
        if base.has(*variables):
            rhs = Pow(Stack(base, *limits).simplify(), Stack(exponent, *limits).simplify())
        else:
            rhs = Pow(base, Stack(exponent, *limits).simplify())
    else:
        rhs = Pow(Stack(base, *limits).simplify(), exponent)


    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a, b = Symbol(real=True, shape=(n,))
    Eq << apply(Stack[j:n](a[j] ** b[j]))

    _j = Symbol('j', domain=Range(n))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[0], _j)





if __name__ == '__main__':
    run()
# created on 2019-10-19
# updated on 2023-06-08
