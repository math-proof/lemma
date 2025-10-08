from util import *


def subs(self, old, new, simplify=True, assumptions={}, index=None, limits=None):
    if self == old:
        return new

    if self.is_Add and old.is_Add:
        this = self._eval_subs(old, new, simplify=simplify, assumptions=assumptions)
        if this is not None:
            return this

    if self.is_Mul and old.is_Mul:
        this = self._eval_subs(old, new, simplify=simplify, assumptions=assumptions)
        if this is not None:
            return this

    if self.is_ExprWithLimits:
        for x, *ab in self.limits:
            if old._has(x):
                domain = assumptions.get(x)
                if domain is False:
                    return self

        self_limits = [*self.limits]
        hit = False
        if limits == self_limits:
            ...
        else:
            for i, [x, *ab] in enumerate(self_limits):
                _ab = [subs(c, old, new, simplify=simplify, assumptions=assumptions, limits=limits) for c in ab]
                if _ab != ab:
                    self_limits[i] = (x, *_ab)
                    hit = True

        expr = subs(self.expr, old, new, simplify=simplify, assumptions=assumptions, limits=limits)
        hit |= expr != self.expr

        if hit:
            self = self.func(expr, *self_limits)
            if simplify:
                self = self.simplify()
        return self

    hit = False
    args = [*self.args]
    if index is None:

        for i, arg in enumerate(args):
            _arg = subs(arg, old, new, simplify=simplify, assumptions=assumptions, limits=limits)
            if _arg != arg:
                hit = True
                args[i] = _arg
    else:
        arg = args[index]
        _arg = subs(arg, old, new, simplify=simplify, assumptions=assumptions, limits=limits)
        if _arg != arg:
            hit = True
            args[index] = _arg

    if hit:
        return self.func(*args, **self.kwargs)

    return self


@apply
def apply(All_Eq, f_eq, reverse=False, simplify=True, assumptions={}):
    assert not f_eq.is_Quantifier
    (lhs, rhs), *limits = All_Eq.of(All[Equal])
    if reverse:
        lhs, rhs = rhs, lhs
    cond = subs(f_eq, lhs, rhs, simplify=simplify, assumptions=assumptions, limits=limits)

    if (ret := std.deleteIndices(limits, lambda limit: not cond._has(limit[0]))) is not None:
        limits = ret
        if not limits:
            return cond

    return All(cond, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    m, n = Symbol(integer=True, positive=True)
    a, b, c = Symbol(real=True, shape=(m, n))
    f = Function(real=True)
    C, S = Symbol(etype=dtype.real[m][n])
    Eq << apply(All[c:C](Equal(a, f(c))), Element(a * b + c, S))

    Eq << Algebra.All.And.of.Cond.All.apply(Eq[1], Eq[0])

    Eq << Eq[-1].this.expr.apply(Bool.Cond.of.Eq.Cond.subst)





if __name__ == '__main__':
    run()
# created on 2019-01-06
# updated on 2023-05-03
