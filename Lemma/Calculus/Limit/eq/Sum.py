from util import *


def doit(cls, self, simplify=True):
    from sympy.concrete.limits import limits_dict
    (expr, *limits), limit = self.of(Limit[cls])

    x = limit[0]
    
    hit = False
    for _x, *ab in reversed(limits):
        if x == _x:
            assert any(c._has(x) for c in ab)
            hit = True

    if not hit and expr._has(x):
        expr = Limit(expr, limit)
        if simplify:
            try:
                expr = expr.doit()
            except:
                ...
                    
    for i, (x, *ab) in enumerate(limits):
        for j, t in enumerate(ab):
            t = Limit(t, limit)
            if simplify:
                t = t.doit()
            ab[j] = t
        limits[i] = (x, *ab)

    return cls(expr, *limits)

@apply
def apply(self, simplify=True):
    return Equal(self, doit(Sum, self, simplify=simplify), evaluate=False)


@prove(proved=False)
def prove(Eq):
    k, n = Symbol(integer=True)
    s = Function(real=True)
    Eq << apply(Limit[n:oo](Sum[k:n](s(k))))


if __name__ == '__main__':
    run()
# created on 2020-03-15
