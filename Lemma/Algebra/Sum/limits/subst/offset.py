from util import *


def limits_subs(cls, self, index, offset, simplify=True):
    if offset is None:
        offset = index
        index = 0

    fx, *limits = self.of(cls)
    limits_former = limits[:index]
    limits_latter = limits[index + 1:]
    x, *ab = limits[index]
    x_offset = x + offset
    fx = fx._subs(x, x_offset)
    if len(ab) == 2:
        a, b = ab
        if a.is_bool:
            a = a._subs(x, x_offset)
            b -= offset
        else:
            a -= offset
            b -= offset
        limit = (x, a, b)
    elif ab:
        domain, = ab
        if domain.is_bool:
            domain = domain._subs(x, x_offset)
        else:
            domain -= offset
        limit = (x, domain)
    else:
        limit = (x,)
        
    for i, (v, *ab) in enumerate(limits_former):
        hit = False
        for j, c in enumerate(ab):
            _c = c._subs(x, x_offset)
            if _c != c:
                hit = True
                ab[j] = _c
                
        if hit:
            limits_former[i] = v, *ab 

    self = cls(fx, *limits_former, limit, *limits_latter)
    if simplify:
        self = self.simplify()
    return self

@apply
def apply(self, index=0, offset=None):
    return Equal(self, limits_subs(Sum, self, index, offset), evaluate=False)


@prove
def prove(Eq):
    a, b, n, d = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(Sum[n:a:b](f(n)), d)

    Eq << Eq[0] - Eq[0].lhs


if __name__ == '__main__':
    run()
# created on 2018-04-28
