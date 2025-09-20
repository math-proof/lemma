from util import *


@apply
def apply(self, old, new):
    from sympy.concrete.limits import limits_sort
    function, *limits = self.of(Any)
    assert not new.is_given
    assert not self.expr._has(new)

    limits_dict = self.limits_dict
    assert new not in limits_dict

    keys = old.free_symbols & limits_dict.keys()

    assert keys

    function = function._subs(old, new)
    assert not function.has(*keys)

    for key in keys:
        assert not limits_dict[key]
        del limits_dict[key]

    limits_dict[new] = None

    limits = limits_sort(limits_dict)

    return Any(function, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    e, a, b = Symbol(real=True)

    A = Function(etype=dtype.real)
    B = Symbol(etype=dtype.real, given=True)

    x = Symbol(integer=True)
    f, g = Function(shape=(), integer=True)

    Eq << apply(Any[e, a:A(b), b:B](f(e) * a > g(f(e)) * b), f(e), x)

    Eq << Algebra.Any.given.Any.subst.apply(Eq[1], x, f(e))

    Eq << ~Eq[-1]

    Eq << Logic.Any_And.of.Any.All.All_Imp.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

# created on 2019-02-18
