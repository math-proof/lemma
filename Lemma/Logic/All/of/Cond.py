from util import *


def all(self, x):
    assert not x.is_given
    assert self._has(x)

    if x.is_bounded:
        _x = x.unbounded
        return ForAll(self._subs(x, _x), (_x, x.domain))
    else:
        return ForAll(self, (x,))

@apply
def apply(given, var=None):
    if var is None:
        var = given.wrt
    assert var.is_symbol
    return all(given, var)


@prove(provable=False)
def prove(Eq):
    from Lemma import Logic

    e = Symbol(positive=True)
    f = Function(integer=True)
    Eq << apply(f(e) > 0)

    Eq << Logic.All.given.All_Or_Not.apply(Eq[1])





if __name__ == '__main__':
    run()

# created on 2018-02-18
# updated on 2021-12-01
