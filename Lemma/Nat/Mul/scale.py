from util import *


@apply(simplify=False)
def apply(self, index=0, scale=None):
    if scale is None:
        scale = index
        index = 0
        
    scale = sympify(scale)
    assert scale.is_nonzero
    
    [*args] = self.of(Mul)
    if index < 0:
        index += len(args)
        
    factor = args[index]
    
    if factor.is_Add:
        ...
    else:
        for index, factor in enumerate(args):
            if factor.is_Add:
                break
        else:
            return
    
    args[index] = Add(*(arg * scale for arg in factor.args))
        
    return Equal(self, Mul(*args) / scale, evaluate=False)


@prove
def prove(Eq):
    a, b, c, d = Symbol(real=True)
    Eq << apply((a / 2 + b / 2 - c) * d, scale=2)

    Eq << Eq[0].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()

    


if __name__ == '__main__':
    run()
# created on 2023-06-03
