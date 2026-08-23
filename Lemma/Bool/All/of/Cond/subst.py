from util import *


@apply(simplify=False)
def apply(given, old, new):
    assert given._has(old)
    assert new.is_symbol
    return All[new:{old}](given._subs(old, new))


@prove
def prove(Eq):
    S = Symbol(etype=dtype.real)
    e = Symbol(real=True)
    e_ = Symbol("e'", real=True)
    f = Function(shape=(), integer=True)

    Eq << apply(f(e) > 0, e, e_)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

# created on 2021-09-17
