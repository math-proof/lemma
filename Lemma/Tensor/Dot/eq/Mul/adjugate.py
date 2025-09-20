from util import *



@apply
def apply(A):
    n = A.shape[0]
    return Equal(A @ Cofactors(A).T, Determinant(A) * Identity(n))


@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    A = Symbol(complex=True, shape=(n, n))
    Eq << apply(A)


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html
# created on 2020-02-10
