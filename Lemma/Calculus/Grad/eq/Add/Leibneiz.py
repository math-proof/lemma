from util import *


@apply
def apply(self, *, simplify=True):
    (ft, (t, a, b)), (x, S[1]) = self.of(Derivative[Integral])
    assert b._has(x) or a._has(x)
    db = Derivative[x](b)
    da = Derivative[x](a)
    if simplify:
        db = db.simplify()
        da = da.simplify()
    return Equal(self, ft._subs(t, b) * db - ft._subs(t, a) * da)


@prove(proved=False)
def prove(Eq):
    x, t, a = Symbol(real=True)
    f, h, g = Function(real=True)
    Eq << apply(Derivative[x](Integral[t:g(x):h(x)](f(t))))


if __name__ == '__main__':
    run()
# created on 2021-08-17
