from util import *


@apply
def apply(self):
    from Lemma.Bool.All_In_Insert.Is.And_All import doit
    return Equal(self, doit(Cap, self))


@prove
def prove(Eq):
    from Lemma import Set
    x = Symbol(etype=dtype.real, shape=(oo, oo))
    i, j, a, b, c, d = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    Eq << apply(Cap[j:{a, b, c, d}, i:m](x[i, j]))

    @Function(etype=dtype.real)
    def s(i):
        return Cap[j:{a, b, c, d}](x[i, j])

    Eq << s(i).this.defun()

    Eq << Set.EqCap.of.Eq.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(Set.Cap.eq.Inter.doit.setlimit)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-01-18
