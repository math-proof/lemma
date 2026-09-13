from util import *


def sigmar(conds, k):
    from std.combinatorics import generate_combination
    from _functools import reduce
    
    if k == 0:
        return 1

    if k == 1:
        return sum(Pr(cond) for cond in conds)

    sigmar = 0
    for indices in generate_combination(len(conds), k):
        sigmar += Pr(reduce(lambda x, y: x & y, (conds[i] for i in indices)))
    return sigmar


@apply
def apply(self):
    conds = self.of(Pr[Or])
    sgm = 0
    coeff = 1
    for k in range(len(conds)):
        sgm += sigmar(conds, k + 1) * coeff
        coeff *= -1
       
    return Equal(self, sgm)


@prove(proved=False)
def prove(Eq):
    x, y = Symbol(real=True, random=True)
    a, b = Symbol(real=True)
    Eq << apply(Pr((x >= a) | (y <= b)))

    


if __name__ == '__main__':
    run()
# created on 2023-04-18
