from util import *


@apply
def apply(given, simplify=True, index=-1):
    et, *limits = given.of(All[And])
    eqs = []
    for eq in et:
        forall = All(eq, *limits)
        if simplify:
            forall = forall.simplify()
        eqs.append(forall)
    first = eqs[:index]
    second = eqs[index:]
    return And(*first), And(*second)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic, Bool

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    A = Symbol(etype=dtype.real[k])
    f, g = Function(real=True)
    b = Symbol(shape=(k,), real=True)
    Eq << apply(All[x:A](And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b))))

    Eq << Bool.And_And.of.And.apply(Eq[1], 1)

    Eq <<= Eq[-1] & Eq[-2] & Eq[2]




if __name__ == '__main__':
    run()

# created on 2018-09-29
