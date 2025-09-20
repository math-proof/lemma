from util import *


@apply
def apply(self, offset=None):
    fx, (x, *ab) = self.of(Measure[Cup[FiniteSet]])
    if offset is None:
        offset = []
        for arg in fx.of(Add):
            if not arg._has(x):
                offset.append(arg)
        offset = -Add(*offset)
    else:
        assert not offset._has(x)

    if len(ab) == 2:
        a, b = ab
        assert a.is_bool
        b = Element(x, b)
        ab = [a & b]
    return Equal(self, Measure(imageset(x, fx + offset, *ab).simplify()))


@prove(proved=False)
def prove(Eq):
    x, h = Symbol(real=True)
    f = Function(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(Measure(imageset(x, f(x) + h, S)))


if __name__ == '__main__':
    run()
# created on 2020-05-22
