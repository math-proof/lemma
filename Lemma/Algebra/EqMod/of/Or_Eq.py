from util import *


@apply
def apply(given):
    (x, a), (_x, b) = given.of(Equal | Equal)
    if x != _x:
        if x == b:
            _x, b = b, _x
        else:
            x, a = a, x
            if x != _x:
                _x, b = b, _x
        assert x == _x

    assert x.is_integer and a.is_integer and b.is_integer
    d = abs(a - b)
    assert d > 0
    return Equal(x % d, a % d)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(Equal(x, a) | Equal(x, a + 3))

    Eq << Eq[0].this.args[0].apply(Algebra.EqMod.of.Eq, 3)

    Eq << Eq[-1].this.args[0].apply(Algebra.EqMod.of.Eq, 3)




if __name__ == '__main__':
    run()
# created on 2018-11-22
# updated on 2023-05-20
