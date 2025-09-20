from util import *


@apply
def apply(eq_conditioned, i=None, y=None):
    ((x, k), S[x[:k].as_boolean()]), S[x[k]] = eq_conditioned.of(Equal[Conditioned[Indexed]])
    if i is None:
        i = eq_conditioned.generate_var(integer=True)
    if y is None:
        y = eq_conditioned.generate_var(**x[k].dtype.dict)
    return Equal(x[k] | Equal(Sum[i:k](x[i] ** 2), y), x[k])


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True, shape=(oo,), random=True)
    n = Symbol(integer=True, given=False)
    i = Symbol(integer=True)
    Eq << apply(Equal(x[n] | x[:n], x[n]), i)

    


if __name__ == '__main__':
    run()
# created on 2023-06-19
