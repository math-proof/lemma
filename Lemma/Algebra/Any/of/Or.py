from util import *


def ou_to_any(imply):
    from sympy.concrete.limits import limits_union
    exists = imply.of(boolalg.Or)
    fn = set()
    limitsArr = []
    for exist in exists:
        func, *_limits = exist.of(Any)
        fn.add(func)
        assert len(fn) == 1

        limitsArr.append(_limits)

    limits = limitsArr[0]
    for i in range(1, len(limitsArr)):
        limits = limits_union(limits, limitsArr[i])

    fn, *_ = fn
    return Any(fn, *limits)


@apply
def apply(imply):
    return ou_to_any(imply)


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real, given=True)
    f = Function(integer=True)

    Eq << apply(boolalg.Or(Any[x:A](f(x) > 0), Any[x:B](f(x) > 0)))

    Eq << ~Eq[1]

    Eq << ~Eq[0]

    Eq << Eq[-1].this.apply(Algebra.And.Is.All.limits.Union)


if __name__ == '__main__':
    run()

# created on 2020-02-18
del Or
