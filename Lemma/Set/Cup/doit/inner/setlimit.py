from util import *


@apply
def apply(self):
    from Lemma.Bool.All_In_Insert.Is.And_All import doit
    return Equal(self, doit(Cup, self))


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(etype=dtype.real, shape=(oo, oo))
    i, j, a, b, c, d = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    Eq << apply(Cup[j:{a, b, c, d}, i:m](x[i, j]))

    @Function(etype=dtype.real)
    def s(i):
        return Cup[j:{a, b, c, d}](x[i, j])

    Eq << s(i).this.defun()

    Eq << Set.EqCupS.of.All_Eq.fin.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(Set.Cup.eq.Union.doit.setlimit)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()

# created on 2021-02-05
# updated on 2022-04-03
