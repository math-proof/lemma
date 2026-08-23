from util import *


def rewrite(Sum, self):
    expr, (i, *_), (j, *_) = self.of(Sum)
    assert i.type == j.type
    z = Dummy('z', **i.type.dict)
    this = self.limits_subs(i, z, simplify=None)
    this = this.limits_subs(j, i, simplify=None)
    this = this.limits_subs(z, j, simplify=None)
    return this

@apply
def apply(self):
    return Equal(self, rewrite(Sum, self))


@prove
def prove(Eq):
    i, j, k = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    f = Function(integer=True)
    g = Symbol(shape=(oo, oo), real=True)
    h = Symbol(shape=(oo,), real=True)
    Eq << apply(Sum[i:f(j), j:A](h[i] * g[i, j]))

    Eq << Eq[-1].this.rhs.limits_subs(i, k)

    
    


if __name__ == '__main__':
    run()

# created on 2019-11-08
# updated on 2023-05-25
