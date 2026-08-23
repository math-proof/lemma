from util import *


@apply
def apply(given):
    (function, (y, Sy)), (x, Sx) = given.of(All[Any])

    z = Dummy('z', **y.type.dict)
    function = function._subs(y, z)
    function = function._subs(x, y)
    function = function._subs(z, x)
    assert not Sy._has(x)

    return All[y:Sx](Any[x:Sy](function))


@prove
def prove(Eq):
    k = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(k,), etype=dtype.integer)

    f, g = Function(shape=(), integer=True)

    S_x, S_y = Symbol(etype=dtype.integer.set[k])

    Eq << apply(All[x:S_x](Any[y:S_y](Equal(f(x), g(y)))))

    Eq << Eq[1].limits_subs(y, Dummy('y', **y.type.dict))


if __name__ == '__main__':
    run()

# created on 2021-09-19
