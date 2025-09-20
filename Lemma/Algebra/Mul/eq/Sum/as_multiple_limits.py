from util import *


@apply
def apply(self):
    (fi, (i, *iab)), (fj, (j, *jab)) = self.of(Sum * Sum)
    if i == j:
        _j = self.generate_var(excludes=i, integer=True)
        fj = fj._subs(j, _j)
        j = _j

    rhs = Sum((fi * fj).powsimp(), (i, *iab), (j, *jab))
    return Equal(self, rhs, evaluate=False)



@prove
def prove(Eq):
    from Lemma import Algebra

    n, m = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Sum[i:m](f(i)) * Sum[i:n](g(i)))

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()
# created on 2020-02-02
