from util import *


@apply
def apply(eq, distributed_x, distributed_y):
    ((Λ_x, Λ_xy), (S[Λ_xy.T], Λ_y)), ((Σ_x, Σ_xy), (S[Σ_xy.T], Σ_y)) = eq.of(Equal[BlockMatrix[BlockMatrix[1], BlockMatrix[1]], MatPow[BlockMatrix[BlockMatrix[1], BlockMatrix[1]], -1]])
    assert Σ_x.is_invertible and Σ_y.is_invertible
    x, S[Σ_x] = distributed_x.of(Distributed[NormalDistribution[Zeros]])
    y, S[Σ_y] = distributed_y.of(Distributed[NormalDistribution[Zeros]])
    n, = x.shape
    m, = y.shape
    return Distributed(BlockMatrix(x, y), NormalDistribution(Zeros(n + m), BlockMatrix([[Σ_x, Σ_xy], [Σ_xy.T, Σ_y]])))

@prove(proved=False)
def prove(Eq):
    m, n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(n,), real=True, random=True)
    y = Symbol(shape=(m,), real=True, random=True)
    Σ_x = Symbol(shape=(n, n), real=True, singular=False)
    Λ_x = Symbol(shape=(n, n), real=True)
    Σ_y = Symbol(shape=(m, m), real=True, singular=False)
    Λ_y = Symbol(shape=(m, m), real=True)
    Σ_xy, Λ_xy = Symbol(shape=(n, m), real=True)
    Eq << apply(Equal(BlockMatrix([[Λ_x, Λ_xy], [Λ_xy.T, Λ_y]]), Inverse(BlockMatrix([[Σ_x, Σ_xy], [Σ_xy.T, Σ_y]]))),
               Distributed(x, NormalDistribution(Zeros(n), Σ_x)),
               Distributed(y, NormalDistribution(Zeros(m), Σ_y)))

    


if __name__ == '__main__':
    run()
# created on 2023-04-30
# updated on 2023-10-03
