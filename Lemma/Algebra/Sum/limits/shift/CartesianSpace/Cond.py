from util import *


@apply
def apply(self):
    function, ((x, (start, stop)), cond, (domain, *shape)) = self.of(Sum[Tuple[Sliced, CartesianSpace]])

    n, = shape
    assert start + 1 < stop
    assert n == stop - start

    return Equal(self, Sum[x[start]:cond:domain, x[start + 1:stop]:CartesianSpace(domain, n - 1)](function))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    a, b = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n - 1))
    x = Symbol(integer=True, shape=(oo,))
    f, g = Function(real=True, shape=())
    Eq << apply(Sum[x[i:n]:g(x[i:n]) > 0:CartesianSpace(Range(a, b + 1), n - i)](f(x[i:n])))

    Eq << Eq[0].this.lhs.apply(Algebra.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.rhs.find(Element[Sliced]).apply(Set.In_CartesianSpace.Is.All.In)

    Eq << Eq[-1].this.rhs.find(All).apply(Algebra.All.limits.subst.offset, -i - 1)

    Eq << Eq[-1].this.lhs.find(Element[Sliced]).apply(Set.In_CartesianSpace.Is.All.In)

    Eq << Eq[-1].this.lhs.find(All).apply(Algebra.All.limits.subst.offset, -i)

    Eq << Eq[-1].this.lhs.find(All).apply(Algebra.All.Is.And.split, cond={i})

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.shift.Slice)





if __name__ == '__main__':
    run()

# created on 2020-03-18
# updated on 2023-07-02
