from util import *


def rewrite(Sum, self, i):
    expr, *limits = self.of(Sum)
    [x_lhs], [x_rhs] = limits[i:i + 2]
    if x_lhs.is_Sliced:
        x, (start, stop) = x_lhs.args
        if x_rhs.is_Sliced:
            S[x], (start_, stop_) = x_rhs.args
            if stop == start_:
                stop = stop_
            elif stop_ == start:
                start = start_
            else:
                return
        elif x_rhs.is_Indexed:
            S[x], index = x_rhs.args
            if index == stop:
                stop += 1
            elif index == start - 1:
                start = index
            else:
                return
        else:
            return
    elif x_lhs.is_Indexed:
        x, index = x_lhs.args
        if x_rhs.is_Sliced:
            S[x], (start, stop) = x_rhs.args
            if index == stop:
                stop += 1
            elif index == start - 1:
                start = index
            else:
                return
        elif x_rhs.is_Indexed:
            S[x], index_ = x_rhs.args
            if index == index_ + 1:
                start = index_
                stop = index + 1
            elif index == index_ - 1:
                start = index
                stop = index_ + 1
            else:
                return
        else:
            return

    limits.pop(i)
    limits[i] = x[start:stop],
    return Sum(expr, *limits)

@apply
def apply(self, index=0):
    return Equal(self, rewrite(Sum, self, index))


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n - 1))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Sum[x[i], x[i + 1:n + 1]](f(x[i:n])))

    Eq << Eq[0].this.rhs.apply(Algebra.Sum.limits.shift.Slice)


if __name__ == '__main__':
    run()
# created on 2023-03-28
