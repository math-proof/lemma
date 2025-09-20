from util import *



@apply
def apply(imply):
    e, interval = imply.of(Element)

    return Element(-e, -interval)


@prove
def prove(Eq):
    from Lemma import Set
    x = Symbol(integer=True)
    a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Set.Neg.In.IccNegS.of.In_Icc.apply(Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-10-05
