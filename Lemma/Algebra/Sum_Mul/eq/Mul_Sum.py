from util import *


@apply
def apply(self, *, simplify=True):
    coefficient = []
    factors = []
    args, *limits = self.of(Sum[Mul])
    variables = [v for v, *_ in limits]
    for arg in args:
        if not arg.has(*variables):
            coefficient.append(arg)
        elif arg.is_Pow and arg.exp.is_Add and any(not exp.has(*variables) for exp in arg.exp.args):
            base = arg.base
            _factors, _coefficient = std.array_split(arg.exp.args, lambda arg: arg.has(*variables))
            factors += [base ** arg for arg in _factors]
            coefficient += [base ** arg for arg in _coefficient]
        else:
            factors.append(arg)

    if not coefficient:
        return

    return Equal(self, Mul(*coefficient, self.func(Mul(*factors), *self.limits)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra
    i, j = Symbol(integer=True)

    C = Symbol(etype=dtype.integer, given=True)

    f, h = Function(real=True)

    Eq << apply(Sum[i:C](f(i) * h(j)))

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Sum.eq.Sum_Mul)

if __name__ == '__main__':
    run()
# created on 2018-02-15
