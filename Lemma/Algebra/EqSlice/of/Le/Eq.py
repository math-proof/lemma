from util import *


@apply
def apply(le, eq, start=0, step=1):
    stop, n = le.of(LessEqual)
    a, b = eq.of(Equal)
    assert a.shape == b.shape
    assert n <= a.shape[0] == b.shape[0]
    if step == 1:
        return Equal(a[start:stop], b[start:stop])
    return Equal(a[start:stop:step], b[start:stop:step])

@prove
def prove(Eq):
    k, n, d = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(n,))
    Eq << apply(LessEqual(k, n), Equal(x, y), step=d)

    Eq << Eq[-1].subs(Eq[1])

    
    


if __name__ == '__main__':
    run()

# created on 2020-12-30
# updated on 2021-12-27