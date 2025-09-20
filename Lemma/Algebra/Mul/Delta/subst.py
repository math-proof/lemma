from util import *


@apply
def apply(self, index=None, reverse=False):
    [*array] = self.of(Mul)
    if index is None:
        for index, expr in enumerate(array):
            if args := expr.of(KroneckerDelta):
                old, new = args
                break
        else:
            return
    else:
        old, new = array[index].of(KroneckerDelta)

    if reverse:
        old, new = new, old

    delta = array.pop(index)

    rest = Mul(*array)

    rest_ = rest.subs(old, new)
    if rest_ == rest_:
        rest = rest_.subs(new, old)
    else:
        rest = rest_

    return Equal(self, rest * delta, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(integer=True)
    f = Function(complex=True)
    Eq << apply(f(y) * f(x) * KroneckerDelta(x, y))

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.eq.Ite)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Ite)




if __name__ == '__main__':
    run()
# created on 2023-03-17
# updated on 2023-06-08
