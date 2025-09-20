from util import *



@apply
def apply(A):
    n = A.shape[0]
    i, j = Symbol(integer=True)
    d = Symbol(shape=(oo,), integer=True)
    k = Symbol(domain=Range(n))
    return Equal(Sum[k:1:n + 1]((-1) ** (k + 1) * Sum[d[:k]:All[j:i, i:k](d[j] < d[i]):CartesianSpace(Range(n), k)](Card(Cap[i:k](A[d[i]])))),
                    Card(Cup[i:n](A[i])))


@prove(proved=False)
def prove(Eq):
    n = Symbol(domain=Range(2, oo))
    A = Symbol(etype=dtype.integer, shape=(n,))

    Eq << apply(A)

    Eq << Eq[0].subs(n, 2)


if __name__ == '__main__':
    run()

# created on 2021-04-23
