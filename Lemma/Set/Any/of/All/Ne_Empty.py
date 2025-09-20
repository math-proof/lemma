from util import *


@apply
def apply(is_nonempty, all):
    s = is_nonempty.of(Unequal[EmptySet])
    function, (e, *rhs) = all.of(All)

    if len(rhs) == 2:
        S[s] = e.range(*rhs)
    else:
        S[s], = rhs

    return Any[e:s](function)


@prove
def prove(Eq):
    S = Symbol(etype=dtype.integer, given=True)
    e = Symbol(integer=True)
    f = Function(integer=True, shape=())
    Eq << apply(Unequal(S, S.etype.emptySet), All[e:S](f(e) > 0))

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2018-12-01
