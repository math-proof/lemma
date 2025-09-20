from util import *


@apply
def apply(eq, f_eq):
    if not eq.is_Equal:
        eq, f_eq = f_eq, eq
    lhs, rhs = eq.of(Equal)
    _lhs, _rhs = f_eq.of(Unequal)
    return Unequal(_lhs._subs(lhs, rhs), _rhs._subs(lhs, rhs))


@prove
def prove(Eq):
    n, m = Symbol(integer=True, positive=True)
    f, g = Function(real=True, shape=(m,))

    a, b = Symbol(real=True, shape=(n,))
    Eq << apply(Equal(a, b), Unequal(f(a), g(a)))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2020-07-14
