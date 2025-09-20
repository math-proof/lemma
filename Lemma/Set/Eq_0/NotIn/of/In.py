from util import *



@apply
def apply(given):
    return Equal(Bool(given.invert()), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic
    e = Symbol(integer=True)
    s = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, s))

    Eq << Eq[-1].this.lhs.apply(Logic.Bool.eq.Ite)


if __name__ == '__main__':
    run()

# created on 2021-03-10
