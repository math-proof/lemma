from util import *


@apply
def apply(given, index):
    [*eqs], *limits = given.of(Any[And])

    eq = eqs[index]
    del eqs[index]
    wrt, B = eq.of(Element)

    i = given.variables.index(wrt)

    function = And(*eqs)

    A = given.limits_dict[wrt]
    if A:
        limits[i] = (wrt, A & B)
    else:
        limits[i] = (wrt, B)

    return Any(function, *limits)


@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))

    A, B = Symbol(etype=dtype.real[n])

    f = Function(shape=(), integer=True)

    Eq << apply(Any[x[:n]: A](Element(x[:n], B) & (f(x[:n]) > 0)), index=1)

    Eq << Set.Any_And_In.of.Any.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2021-01-16
