from util import *


@apply
def apply(eq_historic, eq_n):
    lhs, rhs = eq_historic.of(Equal)
    n = lhs.shape[0]

    if lhs.is_Stack and rhs.is_Stack and lhs.variable == rhs.variable:
        k = rhs.variable
    else:
        k = eq_historic.generate_var(integer=True)

    fx = lhs[k]
    gy = rhs[k]

    S[fx._subs(k, n)], S[gy._subs(k, n)] = eq_n.of(Equal)
    return Equal(Stack[k:n + 1](fx).simplify(), Stack[k:n + 1](gy).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(Equal(Stack[k:n](f(k)), Stack[k:n](g(k))), Equal(f(n), g(n)))

    Eq << Algebra.Eq.given.And.Eq.Block.apply(Eq[-1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2019-03-24
