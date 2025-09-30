from util import *


@apply
def apply(given, right_open=True):
    x, (a, b) = given.of(Element[Range])
    if right_open:
        return x >= a, x < b
    else:
        return x >= a, x <= b - 1


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(real=True, given=True)
    a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Range(a, b)), False)

    Eq << Set.Le.of.In_Ico.apply(Eq[0])

    Eq << Set.Ge.of.In_Ico.int.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-05-05


from . import split
