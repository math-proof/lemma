from util import *


@apply(simplify=False)
def apply(self, index=0):
    [*args] = self.of(Mul)
    
    if index < 0:
        index += len(args)
        
    factor = args[index]
    
    if factor.is_Pow and factor.base == -1:
        base, exp = factor.args
        args[index] = base ** (exp + 1)
        args.append(-1)
    else:
        if factor.is_Add:
            args.append(-1)
        else:
            args[index] = -factor
    
            for index, factor in enumerate(args):
                if factor.is_Add:
                    break
            else:
                return
        
        args[index] = Add(*(-arg for arg in factor.args))
        
    return Equal(self, Mul(*args), evaluate=False)


@prove
def prove(Eq):
    a, b, c, d = Symbol(real=True)
    Eq << apply((a + b - c) * d)

    Eq << Eq[0].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()

    
    


if __name__ == '__main__':
    run()
# created on 2021-08-02
# updated on 2023-05-02
