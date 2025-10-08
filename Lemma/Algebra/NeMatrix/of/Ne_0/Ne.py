from util import *



@apply
def apply(unequality, eq):
    divisor = unequality.of(Unequal[Determinant, 0])
    lhs, rhs = eq.of(Unequal)
    return Unequal(lhs @ Inverse(divisor), rhs @ Inverse(divisor))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    n = Symbol(integer=True)
    A = Symbol(real=True, shape=(n, n), given=True)
    a, b = Symbol(real=True, shape=(n,), given=True)
    Eq << apply(Unequal(Determinant(A), 0), Unequal(a @ A, b))

    Eq << ~Eq[-1]

    Eq << Bool.Cond.of.Or_Not.Cond.apply(Eq[0], Eq[-1])

    Eq << Eq[-1] @ A

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()
# created on 2020-02-16
