from util import *


@apply
def apply(self):
    expr, (x, eqs) = self.of(Cup[FiniteSet, Tuple[And]])
    return Subset(self, Intersection(*(imageset(x, expr, eq) for eq in eqs)))


@prove
def prove(Eq):
    from Lemma import Set
    n, m = Symbol(integer=True, positive=True)

    x = Symbol(complex=True, shape=(n,))
    f = Function(complex=True, shape=(m,))

    g, h = Function(shape=(), real=True)

    Eq << apply(imageset(x, f(x), (g(x) > 0) & (h(x) > 0)))

    A = Symbol(conditionset(x, g(x) > 0))
    B = Symbol(conditionset(x, h(x) > 0))
    Eq << imageset(x, f(x), A & B).this.subs(A.this.definition)

    Eq << Eq[-1].this.rhs.limits[0][2].definition

    Eq << imageset(x, f(x), A).this.subs(A.this.definition)

    Eq << imageset(x, f(x), B).this.subs(B.this.definition)

    Eq << Set.Imageset_Inter.subset.Inter.apply(imageset(x, f(x), A & B))

    Eq << Eq[-1].subs(Eq[-2], Eq[-3], Eq[-4])


if __name__ == '__main__':
    run()

# created on 2021-04-26
