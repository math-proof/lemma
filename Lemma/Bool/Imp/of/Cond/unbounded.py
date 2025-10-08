from util import *


@apply
def apply(self, var=None):
    if var is None:
        var = self.wrt
    assert var.is_symbol
    assert not var.is_given
    assert self._has(var)

    _var = var.unbounded
    domain = var.domain
    if domain.is_Interval:
        if domain.stop == oo:
            if domain.left_open:
                cond = _var > domain.start
            else:
                cond = _var >= domain.start
        elif domain.start == oo:
            if domain.right_open:
                cond = _var < domain.stop
            else:
                cond = _var <= domain.stop
    else:
        cond = Element(_var, var.domain)
    return Imply(cond, self._subs(var, _var))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x = Symbol(positive=True)
    f = Function(integer=True, shape=())
    Eq << apply(f(x) > 0, x)

    Eq << Bool.All.of.Cond.apply(Eq[0])

    Eq << Bool.Imp.of.AllSetOf.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-03-19
