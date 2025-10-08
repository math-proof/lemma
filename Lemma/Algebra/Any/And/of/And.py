from util import *


@apply(simplify=None)
def apply(given):
    [*eqs] = given.of(And)
    for i, eq in enumerate(eqs):
        if eq.is_Exists:
            break
    else:
        return
    exists = eqs.pop(i)
    f, *limits = exists.of(Any)
    f = And(*eqs, f)
    return Any(f, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    f, g, h = Function(real=True)
    b = Symbol(shape=(k,), real=True)
    B = Symbol(etype=dtype.real[k], given=True)
    Eq << apply(And(Unequal(x, y), Unequal(f(x), g(y)), Any[b:B](Equal(f(x), h(b)))))

    Eq << Eq[0].this.args[1:].apply(Bool.Any_And.of.Any.All, simplify=None)

    Eq << Eq[-1].this.apply(Bool.Any_And.of.Any.All, simplify=None)


if __name__ == '__main__':
    run()
# created on 2019-05-07
