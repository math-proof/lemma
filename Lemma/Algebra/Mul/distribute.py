from util import *


@apply(simplify=False)
def apply(self, index=0):
    [*args] = self.of(Mul)
    factor = args.pop(index)

    for i, plus in enumerate(args):
        if plus.is_Add:
            break
    else:
        return
            
    plus = Add(*(arg * factor for arg in plus.args))
    args[i] = plus
    return Equal(self, Mul(*args))


@prove
def prove(Eq):
    a, b, c, d, r = Symbol(real=True)
    Eq << apply(-r * (a - b - c) / d)

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()

    


if __name__ == '__main__':
    run()
# created on 2018-08-19
# updated on 2022-01-23
