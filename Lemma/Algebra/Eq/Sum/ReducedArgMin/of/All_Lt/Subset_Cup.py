from util import *


@apply
def apply(all_lt, subset, f):
    ((d, j), (S[d], i)), (S[j], S[0], S[i]), (S[i], S[0], m) = all_lt.of(All[Indexed < Indexed])
    cup, (S[0], n) = subset.of(Subset[Expr, Range])     
    (d, j), (S[j], S[0], S[m]) = cup.of(Cup[FiniteSet[Indexed]])    
    return Equal(Sum[j:d[j] > i:Range(m)](f(i, j)).simplify(), Sum[j:ReducedArgMin(d - i + n * Stack[j:m](Bool(d[j] <= i))):m](f(i, j)))


@prove(proved=False)
def prove(Eq):
    n, m = Symbol(integer=True, positive=True)
    d = Symbol(shape=(m,), integer=True)
    i, j = Symbol(integer=True)
    s = d[:m].cup_finiteset(j)
    f = Function(real=True)
    Eq << apply(All[j:i, i:m](d[j] < d[i]), Subset(s, Range(n)), f)

    
    


if __name__ == '__main__':
    run()
# created on 2022-04-26
# updated on 2022-04-30
