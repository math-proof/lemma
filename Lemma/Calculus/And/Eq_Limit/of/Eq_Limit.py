from util import *


@apply
def apply(limited_f):
    (fx, (x, x0)), A = limited_f.of(Equal[Limit])
    assert not x0.infinitesimality
    return Equal(Limit[x:x0 + S.Infinitesimal](fx), A), Equal(Limit[x:x0 - S.Infinitesimal](fx), A)


@prove
def prove(Eq):
    from Lemma import Calculus

    x, x0, A = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(Limit[x:x0](f(x)), A))

    Eq << Calculus.Eq_Limit.of.Eq_Limit.one_sided.apply(Eq[0])

    Eq << Calculus.Eq_Limit.of.Eq_Limit.one_sided.apply(Eq[0], dir=-1)




if __name__ == '__main__':
    run()
# created on 2020-04-27
# updated on 2023-10-15
