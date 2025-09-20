from util import *


@apply
def apply(imply):
    x, (S[x], cond, *baseset) = imply.of(Unequal[Cup[FiniteSet], EmptySet])
    if baseset:
        baseset, = baseset
        return Any[x:baseset](cond)
    else:
        return Any[x](cond)


@prove
def prove(Eq):
    S = Symbol(etype=dtype.complex)
    x = Symbol(complex=True)
    f = Function(real=True)

    Eq << apply(Unequal(conditionset(x, f(x) > 1, S), x.emptySet))

    A = Symbol(Eq[0].lhs)

    Eq << A.this.definition

    Eq << Any[x:S](Element(x, A), plausible=True)

    Eq << Eq[-1].this.expr.subs(Eq[2])

    Eq << Eq[-1].simplify()

    Eq << Eq[-1].subs(Eq[2])


if __name__ == '__main__':
    run()

# created on 2020-11-07
