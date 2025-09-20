from util import *


def rewrite(self, i=None):
    expr = self.of(ReducedSum)
    if i is None:
        i = expr.generate_var(integer=True, excludes={*expr.variables})
    
    return Sum[i:expr.shape[-1]](expr[..., i])
    
@apply
def apply(self, i=None):
    return Equal(self, rewrite(self, i=i), evaluate=False)


@prove(provable=False)
def prove(Eq):
    n, m, k = Symbol(integer=True, positive=True)
    y = Symbol(shape=(m, n, k), real=True)
    Eq << apply(ReducedSum(y))

    
    


if __name__ == '__main__':
    run()
# created on 2019-11-10
# updated on 2023-08-20
