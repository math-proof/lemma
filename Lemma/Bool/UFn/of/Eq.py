from util import *


@apply
def apply(given, function):
    lhs, rhs = given.of(Equal)
    # assert function(lhs).domain_definition()
    # assert function(rhs).domain_definition()
    return Equal(function(lhs), function(rhs))


@prove
def prove(Eq):
    n, m = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(m,))
    x, b = Symbol(real=True, shape=(n,))
    a = Symbol(real=True)
    Eq << apply(Equal(x * a, b), f)

    y = Symbol(f(a * x))
    Eq << y.this.definition

    Eq << Eq[-1].this.rhs.subs(Eq[0])

    Eq << Eq[-1].subs(Eq[-2])


if __name__ == '__main__':
    run()
# created on 2018-04-03
