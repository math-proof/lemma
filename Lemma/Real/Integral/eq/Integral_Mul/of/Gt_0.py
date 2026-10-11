from util import *


def limits_subs(self, old, new, simplify=True):
    expr, (x, a, b) = self.of(Integral)
    
    if old == x:
        expr = expr._subs(old, new)
        if new._has(x):
            a = new._subs(x, a).simplify()
            b = new._subs(x, b).simplify()
        else:
            x, = new.free_symbols - self.free_symbols
            a = Equal(new, a).solve(x)
            a = a.of(Equal[x])
            b = Equal(new, b).solve(x)
            b = b.of(Equal[x])
            
        expr *= diff(new, x)
    elif new == x:
        new = expr.generate_var(real=True)
        expr = expr._subs(old, new)
        expr /= diff(old, x)
        assert not expr._has(x)
        
        expr = expr._subs(new, x)
        new = old

        a = new._subs(x, a).simplify()
        b = new._subs(x, b).simplify()
    else:
        return
        
    self = Integral(expr, (x, a, b))
    if simplify:
        return self.simplify()
    return self

@apply
def apply(self, old, new, *, simplify=True):
    return Equal(self, limits_subs(self, old, new, simplify=simplify), evaluate=False)


@prove(proved=False)
def prove(Eq):
    x, a, b, c = Symbol(real=True)
    t = Symbol(positive=True)
    f = Function(real=True)
    Eq << apply(Integral[x:a:b](f(x)), x, c + t * x)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-18

# updated on 2023-04-30
