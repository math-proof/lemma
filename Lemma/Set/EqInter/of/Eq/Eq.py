from util import *



@apply
def apply(equality_A, equality_B):
    a, b = equality_A.of(Equal)
    x, y = equality_B.of(Equal)

    return Equal(a & x, b & y)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    A, B, X, Y = Symbol(etype=dtype.integer[n])

    Eq << apply(Equal(A, B), Equal(X, Y))

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    run()

# created on 2020-10-02
