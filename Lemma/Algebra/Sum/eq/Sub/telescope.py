from util import *


@apply
def apply(self):
    (_xi, xi), limit = self.of(Sum[Expr - Expr])
    try:
        i, a, b = limit
    except:
        i, = limit
        domain = xi.domain_defined(i)
        a, b = domain.of(Range)

    assert i.is_integer

    if _xi == xi._subs(i, i + 1):
        rhs = xi._subs(i, b) - xi._subs(i, a)
    elif xi == _xi._subs(i, i + 1):
        rhs = _xi._subs(i, a) - _xi._subs(i, b)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset

    x = Function(real=True)
    i, k = Symbol(integer=True)
    n = Symbol(integer=True)
    Eq << apply(Sum[k:i:n + 1](x(k + 1) - x(k)))

    Eq << Eq[-1].this.lhs.apply(Finset.Sum_Add.eq.AddSumS)



    # https://en.wikipedia.org/wiki/Telescoping_series




if __name__ == '__main__':
    run()
# created on 2020-03-24
# updated on 2023-08-19
