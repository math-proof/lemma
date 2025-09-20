from util import *

   
@apply
def apply(self):
        
    X = self.of(Det)
    n = X.shape[0]
    for row in X.of(BlockMatrix):
        axis = 0 if len(row.shape) == 1 else 1
        row = row.of(BlockMatrix[axis])
            
        for cell in row:
            if cell.is_Zeros:
                *_, a, b = cell.shape
                if a + b > n:
                    break
        else:
            continue
        break
    else:
        return

    return Equal(self, 0)


@prove(proved=False)
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    A = Symbol(complex=True, shape=(n, n - 1))
    B = Symbol(complex=True, shape=(n, n + 1))
    C = Symbol(complex=True, shape=(n, n - 1))
    Eq << apply(Determinant(BlockMatrix([[A, B],[C, Zeros(n, n + 1)]])))

    # Algebra.gt.then.lt.add.min
    


if __name__ == '__main__':
    run()
# created on 2020-10-14
# updated on 2022-07-12
