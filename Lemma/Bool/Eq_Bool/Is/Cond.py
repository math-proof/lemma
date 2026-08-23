from util import *



@apply
def apply(given):
    boole, one = given.of(Equal)
    if not one.is_One:
        boole, one = one, boole
    assert one.is_One

    cond = boole.of(Bool)

    return cond


@prove
def prove(Eq):
    from Lemma import Bool
    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)

    Eq << apply(Equal(functions.Bool(Element(x, A)), 1))

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)


if __name__ == '__main__':
    run()
# created on 2019-04-21
