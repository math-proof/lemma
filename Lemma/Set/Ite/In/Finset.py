from util import *


@apply
def apply(self):
    ecs = self.of(Piecewise)
    s = {e for e, _ in ecs}
    return Element(self, s)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y, z, a, b = Symbol(real=True, given=True)
    Eq << apply(Piecewise((x, a > 0), (y, b > 0), (z, True)))

    Eq << Bool.BFn_Ite.given.OrAndS.apply(Eq[0])

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.apply(Bool.OrAndS.of.And_Or)

    Eq << Eq[-1].this.apply(Bool.OrAndS.of.And_Or)




if __name__ == '__main__':
    run()
# created on 2018-11-16
# updated on 2023-04-29
