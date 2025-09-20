from util import *


@apply
def apply(self):
    x, domain = self.of(Element)
    assert domain in Interval(-S.Pi, S.Pi, left_open=True)
    return Equal(Arg(exp(S.ImaginaryUnit * x)), x)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(-S.Pi, S.Pi, left_open=True)))

    Eq << Eq[1].this.lhs.apply(Algebra.Arg.ExpI.eq.Add.Ceil)

    Eq << Set.InDiv.of.In_Icc.apply(Eq[0], 2 * S.Pi)

    Eq << Set.InSub.of.In_Icc.apply(Eq[-1], S.One / 2)

    Eq << Set.EqCeil.of.In_Ioc.apply(Eq[-1])

    Eq << Eq[2].subs(Eq[-1])

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-11-07
