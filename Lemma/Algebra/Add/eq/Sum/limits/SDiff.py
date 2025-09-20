from util import *


@apply
def apply(self):
    (function, *limits_a), (S[function], *limits_b) = self.of(Sum - Sum)

    limits = limits_complement(limits_a, limits_b, function=function)
    return Equal(self, Sum(function, *limits), evaluate=False)


def limits_complement(limits, _limits, function=None):
    new_limits = []
    assert len(limits) == len(_limits)

    for limit, _limit in zip(limits, _limits):
        x, domain = limit.coerce_setlimit(function=function)
        S[x], _domain = _limit.coerce_setlimit(function=function)

        assert _domain in domain
        new_limits.append((x, domain - _domain))

    return new_limits


@prove
def prove(Eq):
    k = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    f = Function(integer=True)
    Eq << apply(Add(Sum[k:A](f(k)), -Sum[k:A & B](f(k))))

    Eq << Eq[0] + Eq[0].find(- ~Sum)


if __name__ == '__main__':
    run()
# created on 2020-05-17
