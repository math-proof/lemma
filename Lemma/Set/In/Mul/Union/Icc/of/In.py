from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d > 0

    e, (dom1, dom2) = given.of(Element[Union])
    e *= d
    dom1 *= d
    dom2 *= d
    return Element(e, dom1 | dom2)


@prove
def prove(Eq):
    from Lemma import Set

    x, a, b, c, d = Symbol(real=True)
    e = Symbol(real=True, positive=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True) | Interval(c, d, right_open=True)), e)

    Eq << Set.OrInS.of.In_Union.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(Set.In.Mul.Icc.of.In, e)

    Eq << Eq[-1].this.args[0].apply(Set.In.Mul.Icc.of.In, e)




if __name__ == '__main__':
    run()
# created on 2021-03-06
# updated on 2023-05-20
