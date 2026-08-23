from util import *

def get_original(expr, a, b, axis=0):
    if expr.is_Sliced:
        X, *slices, (start, S[start + b - a]) = expr.args
        assert len(slices) == axis
        slices.append(slice(start - a, None))
        return X[tuple(slices)]
    
    if expr.is_Add:
        return Add(*(get_original(arg, a, b, axis) for arg in expr.args))

    if expr.is_Mul:
        return Mul(*(get_original(arg, a, b, axis) for arg in expr.args))

@apply
def apply(eq, axis=0):
    ecs, lhs = eq.of(Equal[Piecewise])
    b = ecs[0].cond.lhs
    a = ecs[1].expr.args[0].cond.rhs
    prefix = [slice(None)] * axis
    
    n = [0] * len(ecs)
    X = []# blocks
    for i, (expr, cond) in enumerate(ecs):
        if not cond:
            S[b], n[i] = cond.of(LessEqual)
        
        if i:
            for j, (expr, cond) in enumerate(expr.of(Piecewise)):
                if not cond:
                    S[n[i - j - 1]], S[a] = cond.of(LessEqual)

                if j:
                    S[X[i - j][tuple(prefix + [slice(a - n[i - j - 1], None)])]], \
                    *S[X[i - j + 1:-1]], \
                    S[X[-1][tuple(prefix + [slice(None, b - n[i - 1])])]] = expr.of(BlockMatrix[axis])
                else:
                    X.append(get_original(expr, a - n[i - j - 1], b - n[i - j - 1], axis))
        else:
            X.append(get_original(expr, a, b, axis))
            
    lhs = get_original(lhs, a, b, axis)
    return Equal(lhs, BlockMatrix[axis](X))


@prove
def prove(Eq):
    n0, n1, n2, n3, m = Symbol(positive=True, integer=True)

    A = Symbol(shape=(m, n0), real=True)
    B = Symbol(shape=(m, n1), real=True)
    C = Symbol(shape=(m, n2), real=True)
    D = Symbol(shape=(m, n3), real=True)
    X = Symbol(shape=(m, n0 + n1 + n2 + n3), real=True)
    axis = 1
    b = Symbol(domain=Range(1, n0 + n1 + n2 + n3 + 1))
    a = Symbol(domain=Range(b))
    Eq << apply(Equal(X[:, a:b], BlockMatrix[axis](A, B, C, D)[:, a:b]), axis=axis)

    Eq << Eq[1][:, a:b]

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-29
# updated on 2023-04-30
