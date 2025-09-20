from util import *


@apply
def apply(n, k, s1=None, A=None):
    from sympy.functions.combinatorial.numbers import Stirling
    j = Symbol(domain=Range(k + 1))

    if s1 is None:
        x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
        s1 = Symbol(Cup[x[:k + 1]:Stirling.conditionset(n, k + 1, x)]({x[:k + 1].cup_finiteset()}))

    if A is None:
        x = s1.definition.variable.base
        i = Symbol(integer=True)
        s1_quote = Symbol("s'_1", Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol("x'", Stack[i:k + 1](Piecewise(({n} | x[i], Equal(i, j)), (x[i], True))))
        A = Symbol(Stack[j](Cup[x[:k + 1]:s1_quote]({x_quote.cup_finiteset()})))
    return Equal(Card(s1), Card(A[j]))


@prove(proved=False)
def prove(Eq):
    n, k = Symbol(integer=True, positive=True)
    Eq << apply(n, k)

    i, j = Eq[1].rhs.args[0].cond.args
    x = Eq[1].rhs.args[1].expr.base
    x_hat = Symbol(r"\hat{x}", Stack[i:k + 1](Piecewise((x[i] - {n} , Equal(i, j)), (x[i], True))))
    Eq.x_hat_definition = x_hat.this.definition[i]

    s1 = Eq[0].lhs
    x_quote = Eq[1].lhs.base
    Aj = Eq[3].lhs
    e = Symbol(**s1.etype.dict)


if __name__ == '__main__':
    run()

# created on 2020-10-05
