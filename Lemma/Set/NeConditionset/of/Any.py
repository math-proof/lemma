from util import *


@apply
def apply(given):
    function, (x, S) = given.of(Any)
    return Unequal(conditionset(x, function, S), x.emptySet)


@prove
def prove(Eq):
    S = Symbol(etype=dtype.real)
    e = Symbol(real=True)
    f = Function(shape=(), integer=True)

    Eq << apply(Any[e:S](f(e) > 0))

    Eq << Any[e:S](Element(e, Eq[-1].lhs), plausible=True)

    Eq << Eq[-1].this.expr.simplify()

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2021-08-03
