from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    return Element(-x, -interval)


@prove
def prove(Eq):
    from Lemma import Set, Bool

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq <<= Eq[-2].apply(Bool.Imp.given.Or_Not), Eq[-1].apply(Bool.ImpNot.given.Or)

    Eq << Eq[-2].this.args[0].apply(Set.In_Icc.given.InNeg)

    Eq << Eq[-1].this.args[0].apply(Set.In_Icc.given.InNeg)




if __name__ == '__main__':
    run()

# created on 2018-10-06
# updated on 2023-05-08
