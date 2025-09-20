from util import *


@apply
def apply(self, index=0):
    [*args] = self.args
    A = args[index]
    del args[index]

    return Equal(self, Union(A, *[arg - A for arg in args], evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Set

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(A | B)

    C = Symbol(B - A)
    Eq << C.this.definition.reversed

    Eq << Set.EqUnionS.of.Eq.apply(Eq[-1], A)
    Eq << Eq[0].subs(Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-08-08
