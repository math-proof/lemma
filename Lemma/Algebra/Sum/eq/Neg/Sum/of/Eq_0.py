from util import *


@apply
def apply(is_zero, self, pivot=-1, i=None):
    fn1 = is_zero.of(Equal[0])
    args, (k, S[0], n) = self.of(Sum[Mul])
    n -= 1
    assert n >= 0
    fk, gk = std.array_split(args, pivot)
    fk = Mul(*fk)
    gk = Mul(*gk)
    if i is None:
        i = self.generate_var(integer=True, excludes={k, n})
    assert fn1 == fk._subs(k, n + 1)
    return Equal(self, -Sum[k:n + 1]((fk._subs(k, k + 1) - fk) * Sum[i:k + 1](gk._subs(k, i))))


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, nonnegative=True)
    i, k = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(Equal(f(n + 1), 0), Sum[k:n + 1](f(k) * g(k)), i=i)

    Eq << Eq[1].this.lhs.apply(Algebra.Sum.eq.Add.by_parts, i=i)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-06-03
