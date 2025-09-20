from util import *


@apply
def apply(eq):
    ((d, l), (S[d], u)), (L, U) = eq.of(Equal[Expr * (Expr - 1) + Expr * (Expr - 1) + 1, Expr + Expr - 1])
    return Equal(L, d * (l - 1) + 1), Equal(U, d * (u - 1) + 1)


@prove
def prove(Eq):
    l, u, d, L, U = Symbol(integer=True)
    Eq << apply(Equal(d * (l - 1) + d * (u - 1) + 1, L + U - 1))

    Eq << Eq[0].subs(Eq[1])

    Eq << Eq[-1].simplify()

    Eq << Eq[-1].reversed

    


if __name__ == '__main__':
    run()
# created on 2022-04-02
