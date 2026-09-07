from sympy.core import S, Symbol, Add, sympify, Expr, PoleError, Mul

from sympy.core.exprtools import factor_terms
from sympy.core.numbers import GoldenRatio
from sympy.core.symbol import Dummy
from sympy.functions.combinatorial.factorials import factorial
from sympy.functions.combinatorial.numbers import fibonacci
from sympy.functions.special.gamma_functions import gamma
from sympy.polys import PolynomialError, factor
from sympy.series.order import Order
from sympy.simplify.ratsimp import ratsimp
from sympy.simplify.simplify import together
from .gruntz import gruntz
from sympy.core.cache import cacheit


def limit(e, z, z0, direction=1):
    """Computes the limit of ``e(z)`` at the point ``z0``.

    Parameters
    ==========

    e : expression, the limit of which is to be taken

    z : symbol representing the variable in the limit.
        Other symbols are treated as constants. Multivariate limits
        are not supported.

    z0 : the value toward which ``z`` tends. Can be any expression,
        including ``oo`` and ``-oo``.

    direction : string, optional (default: "+")
        The limit is bi-directional if ``direction="+-"``, from the right
        (z->z0+) if ``direction="+"``, and from the left (z->z0-) if
        ``direction="-"``. For infinite ``z0`` (``oo`` or ``-oo``), the ``direction``
        argument is determined from the direction of the infinity
        (i.e., ``direction="-"`` for ``oo``).

    Examples
    ========

    >>> from sympy import limit, sin, Symbol, oo
    >>> from sympy.abc import x
    >>> limit(sin(x)/x, x, 0)
    1
    >>> limit(1/x, x, 0) # default direction='+'
    oo
    >>> limit(1/x, x, 0, direction="-")
    -oo
    >>> limit(1/x, x, 0, direction='+-')
    Traceback (most recent call last):
        ...
    ValueError: The limit does not exist since left hand limit = -oo and right hand limit = oo

    >>> limit(1/x, x, oo)
    0

    Notes
    =====

    First we try some heuristics for easy and frequent cases like "x", "1/x",
    "x**2" and similar, so that it's fast. For all other cases, we use the
    Gruntz algorithm (see the gruntz() function).

    See Also
    ========

     limit_seq : returns the limit of a sequence.
    """

    if direction == 0:
        llim = Limit[z:z0 - S.Infinitesimal](e).doit(deep=False)
        rlim = Limit[z:z0 + S.Infinitesimal](e).doit(deep=False)
        if llim == rlim:
            return rlim
        else:
            # TODO: choose a better error?
            raise ValueError("The limit does not exist since "
                    "left hand limit = %s and right hand limit = %s"
                    % (llim, rlim))
    else:
        return Limit[z:z0 + S.Infinitesimal * direction](e).doit(deep=False)


def heuristics(e, z, z0, direction):
    """Computes the limit of an expression term-wise.
    Parameters are the same as for the ``limit`` function.
    Works with the arguments of expression ``e`` one by one, computing
    the limit of each and then combining the results. This approach
    works only for simple limits, but it is fast.
    """

    from sympy.calculus.util import AccumBounds
    rv = None
    if abs(z0) is S.Infinity:
        rv = limit(e.subs(z, 1 / z), z, S.Zero, 1 if z0 is S.Infinity else -1)
        if isinstance(rv, Limit):
            return
    elif e.is_Mul or e.is_Add or e.is_Pow or e.is_Function:
        r = []
        for a in e.args:
            l = limit(a, z, z0, direction)
            if l.has(S.Infinity) and l.is_finite is None:
                if isinstance(e, Add):
                    m = factor_terms(e)
                    if not isinstance(m, Mul):  # try together
                        m = together(m)
                    if not isinstance(m, Mul):  # try factor if the previous methods failed
                        m = factor(e)
                    if isinstance(m, Mul):
                        return heuristics(m, z, z0, direction)
                    return
                return
            elif isinstance(l, Limit):
                return
            elif l is S.NaN:
                return
            else:
                r.append(l)
        if r:
            rv = e.func(*r)
            if rv is S.NaN and e.is_Mul and any(isinstance(rr, AccumBounds) for rr in r):
                r2 = []
                e2 = []
                for ii in range(len(r)):
                    if isinstance(r[ii], AccumBounds):
                        r2.append(r[ii])
                    else:
                        e2.append(e.args[ii])

                if len(e2) > 0:
                    from sympy import simplify
                    e3 = simplify(Mul(*e2))
                    l = limit(e3, z, z0, direction)
                    rv = l * Mul(*r2)

            if rv is S.NaN:
                try:
                    rat_e = ratsimp(e)
                except PolynomialError:
                    return
                if rat_e is S.NaN or rat_e == e:
                    return
                return limit(rat_e, z, z0, direction)
    return rv


class Limit(Expr):
    """Represents an unevaluated limit.

    Examples
    ========

    >>> from sympy import Limit, sin, Symbol
    >>> from sympy.abc import x
    >>> Limit(sin(x)/x, x, 0)
    Limit(sin(x)/x, x, 0)
    >>> Limit(1/x, x, 0, direction="-")
    Limit(1/x, x, 0, direction='-')

    """
    is_Punctured = True

    def __new__(cls, e, *limits):
        assert len(limits) == 1
        
        limit = limits[0]
        z, z0 = limit
            
        e = sympify(e)
        z = sympify(z)
        
        assert z.is_symbol and not z.is_given
        
        z0 = sympify(z0)

        obj = Expr.__new__(cls)
        from sympy import Tuple
        obj._args = (e, Tuple(z, z0))
        return obj

    @property
    def direction(self):
        e, (z, z0) = self.args
        infinitesimality = z0.infinitesimality
        if infinitesimality:
            return 1

        if infinitesimality == False:
            return -1
        return 0

    @cacheit
    def _eval_free_symbols(self):
        e, (z, z0) = self.args
        isyms = e.free_symbols - z.free_symbols
        isyms.update(z0.free_symbols)
        return isyms

    def doit(self, **hints):
        """Evaluates the limit.

        Parameters
        ==========

        deep : bool, optional (default: True)
            Invoke the ``doit`` method of the expressions involved before
            taking the limit.

        hints : optional keyword arguments
            To be passed to ``doit`` methods; only used if deep is True.
        """
        from sympy.series.limitseq import limit_seq
        from sympy.functions import RisingFactorial

        e, (z, z0) = self.args
        z0, direction = z0.clear_infinitesimal()

        if direction > 0:
            direction = 1
        elif direction < 0:
            direction = -1

        if z0 is S.ComplexInfinity:
            raise NotImplementedError("Limits at complex infinity are not implemented")

        if hints.get('deep', True):
            e = e.doit(**hints)
            z = z.doit(**hints)
            z0 = z0.doit(**hints)

        if e == z:
            return z0

        if not e.has(z):
            return e

        # gruntz fails on factorials but works with the gamma function
        # If no factorial term is present, e should remain unchanged.
        # factorial is defined to be zero for negative inputs (which
        # differs from gamma) so only rewrite for positive z0.
        if z0.is_extended_positive:
            e = e.rewrite([factorial, RisingFactorial], gamma)

        if e.is_Mul:
            if abs(z0) is S.Infinity:
                e = factor_terms(e)
                e = e.rewrite(fibonacci, GoldenRatio)
                ok = lambda w: (z in w.free_symbols and
                                any(a.is_polynomial(z) or
                                    any(z in m.free_symbols and m.is_polynomial(z)
                                        for m in Mul.make_args(a))
                                    for a in Add.make_args(w)))
                if all(ok(w) for w in e.as_numer_denom()):
                    u = Dummy(positive=True)
                    if z0 is S.NegativeInfinity:
                        inve = e.subs(z, -1 / u)
                    else:
                        inve = e.subs(z, 1 / u)
                    try:
                        r = limit(inve.as_leading_term(u), u, S.Zero, 1)
                        if isinstance(r, Limit):
                            return self
                        else:
                            return r
                    except ValueError:
                        pass

        if e.is_Order:
            return Order(limit(e.expr, z, z0), *e.args[1])

        try:
            if direction == 0:
                r = gruntz(e, z, z0, 1)
                _r = gruntz(e, z, z0, -1)
                if r != _r:
                    raise PoleError()
            else:
                r = gruntz(e, z, z0, direction)
                if r is S.NaN:
                    raise PoleError()
        except (PoleError, ValueError):
            r = heuristics(e, z, z0, direction)
            if r is None:
                return self
        except NotImplementedError:
            return self
        return r

    @property
    def dtype(self):
        expr = self.expr
        if expr.is_set:
            return expr.dtype
        
        from sympy import dtype
        if not expr.is_real:
            return dtype.complex
        return dtype.real

    @property
    def is_set(self):
        return self.expr.is_set
    
    @cacheit
    def _eval_shape(self): 
        return self.args[0].shape

    @property
    def expr(self):
        return self.args[0]

    @property
    def limits(self):
        return self.args[1:]

    @property
    def variable(self):
        return self.args[1][0]

    def _sympystr(self, p):
        e, (z, z0) = self.args
        return "Limit[%s:%s](%s)" % tuple(map(p._print, (z, z0, e)))

    def _lean(self, p):
        e, (z, z0) = self.args
        return "limit [%s:%s](%s)" % tuple(map(p._print, (z, z0, e)))

    def _latex(self, p):
        e, (z, z0) = self.args

        tex = r"\lim\limits_{%s \to %s}" % (p._print(z), p._print(z0))
        
        if e.is_Add:
            return r"%s\left(%s\right)" % (tex, p._print(e))
        else:
            return r"%s %s" % (tex, p._print(e))

    def _pretty(self, p):
        e, (z, z0) = self.args
        from sympy.printing.precedence import precedence, PRECEDENCE
        from sympy.printing.pretty.stringpict import prettyForm

        E = p._print(e)
        if precedence(e) <= PRECEDENCE["Mul"]:
            E = prettyForm(*E.parens('(', ')'))
        Lim = prettyForm('lim')

        LimArg = p._print(z)
        if p._use_unicode:
            LimArg = prettyForm(*LimArg.right(u'\N{BOX DRAWINGS LIGHT HORIZONTAL}\N{RIGHTWARDS ARROW}'))
        else:
            LimArg = prettyForm(*LimArg.right('->'))
        LimArg = prettyForm(*LimArg.right(p._print(z0)))

        if dir == 0 or z0 in (S.Infinity, S.NegativeInfinity):
            dir = ""
        else:
            if p._use_unicode:
                dir = u'\N{SUPERSCRIPT PLUS SIGN}' if dir == 1 else u'\N{SUPERSCRIPT MINUS}'

        LimArg = prettyForm(*LimArg.right(p._print(dir)))

        Lim = prettyForm(*Lim.below(LimArg))
        Lim = prettyForm(*Lim.right(E), binding=prettyForm.MUL)

        return Lim

    def simplify(self, **kwargs):
        expr, (x, x0) = self.args
        if not expr._has(x):
            return expr
        
        if expr.is_symbol:
            if expr == x:
                return x0.clear_infinitesimal()[0]
            
        if expr.is_Add:
            const = []
            args = []
            for arg in expr.args:
                if arg._has(x):
                    args.append(arg)
                else:
                    const.append(arg)
            if const:
                expr = Add(*args)
                const = Add(*const)
                if expr == x:
                    return x0.clear_infinitesimal()[0] + const
                
                return Limit[x:x0](expr) + const

        if expr.is_Product or expr.is_Sum or expr.is_Integral:
            function = expr.expr
            limits = [list(limit) for limit in expr.limits]
            hit = False
            for _x, *ab in reversed(limits):
                if x == _x:
                    assert any(c._has(x) for c in ab)
                    hit = True
            if not hit and function._has(x):
                function = Limit[x:x0](function)
                try:
                    function = function.doit()
                except:
                    ...
            for i, (_x, *ab) in enumerate(limits):
                for j, t in enumerate(ab):
                    try:
                        t = Limit[x:x0](t).doit()
                    except:
                        t = Limit[x:x0](t)
                    ab[j] = t
                limits[i] = (_x, *ab)
            expr = expr.func(function, *limits)
            return expr.simplify(**kwargs)

        return self

    @cacheit
    def _has(self, pattern):
        """Helper for .has()"""        
        from sympy.core.assumptions import BasicMeta
        from sympy.core.function import UndefinedFunction
        if isinstance(pattern, (BasicMeta, UndefinedFunction)):
            return Expr._has(self, pattern)
        
        from sympy.tensor.indexed import Indexed, Sliced
        if not isinstance(pattern, (Symbol, Indexed, Sliced)):
            return Expr._has(self, pattern)

        expr = self.expr
        limits = []
        
        for limit in self.limits:
            x, *_ = limit
            if x == pattern:
                return False
            
            limits.append(limit)
                    
        boolean = expr._has(pattern)

        return boolean or any(arg._has(pattern) for arg in limits)

    def _subs(self, old, new, **hints):
        if old == self.variable:
            return self
        
        return Expr._subs(self, old, new, **hints)
    
    def _eval_is_super_real(self):
        return self.expr.is_super_real
    
    def _eval_is_random(self):
        if self.expr.is_random:
            return True

        for x, *ab in self.limits:
            for v in ab:
                if v.is_random:
                    return True

    def _eval_is_extended_negative(self):
        is_extended_negative = self.expr.is_extended_negative
        if is_extended_negative == False:
            return False

    def _eval_is_extended_positive(self):
        is_extended_positive = self.expr.is_extended_positive
        if is_extended_positive == False:
            return False

    def yield_random_symbols(self):
        limits = self.limits
        for v in self.expr.yield_random_symbols():
            if v.is_Indexed:
                x, *indices = v.args
                slices = [*indices]
                is_random = False
                for i, index in enumerate(indices):
                    if index.is_random:
                        is_random = True
                        break

                    for v, *ab in limits:
                        if index._has(v):
                            if v.is_integer and ab and len(ab) == 2 and not isinstance(slices[i], slice):
                                a, b = ab
#                                 f(x) = k * x + h
                                h, k = slices[i].of_simple_poly(v)
                                if k:
                                    if k > 0:
                                        start = slices[i]._subs(v, a)
                                        stop = slices[i]._subs(v, b)
                                        slices[i] = slice(start, stop, k)
                                    elif k < 0:
                                        stop = slices[i]._subs(v, a - 1)
                                        start = slices[i]._subs(v, b - 1)
                                        slices[i] = slice(start, stop, -k)
                                    else:
                                        slices[i] = slice(None)
                                else:
                                    slices[i] = slice(None)
                            else:
                                slices[i] = slice(None)
                                break
                    
                if is_random:
                    yield v
                else:
                    yield x[tuple(slices)]

            else:
                yield v

        for x, *ab in limits:
            for v in ab:
                yield from v.yield_random_symbols()

    def yield_effective_variable(self, variable):
        limits = self.limits
        for v in self.expr.yield_effective_variable(variable):
            if v.is_Indexed:
                x, *indices = v.args
                slices = [*indices]
                is_random = False
                for i, index in enumerate(indices):
                    if index.is_random:
                        is_random = True
                        break

                    for v, *ab in limits:
                        if index._has(v):
                            if v.is_integer and ab and len(ab) == 2 and not isinstance(slices[i], slice):
                                a, b = ab
#                                 f(x) = k * x + h
                                h, k = slices[i].of_simple_poly(v)
                                if k:
                                    if k > 0:
                                        start = slices[i]._subs(v, a)
                                        stop = slices[i]._subs(v, b)
                                        slices[i] = slice(start, stop, k)
                                    elif k < 0:
                                        stop = slices[i]._subs(v, a - 1)
                                        start = slices[i]._subs(v, b - 1)
                                        slices[i] = slice(start, stop, -k)
                                    else:
                                        slices[i] = slice(None)
                                else:
                                    slices[i] = slice(None)
                            else:
                                slices[i] = slice(None)
                                break
                    
                if is_random:
                    yield v
                else:
                    yield x[tuple(slices)]

            else:                    
                yield v

        for x, *ab in limits:
            for v in ab:
                yield from v.yield_effective_variable(variable)

    def limits_in_context(self, has_args=None, parent=None):
        limits = []
        from sympy import Range, Interval, oo
        for z, z0 in reversed(self.limits):
            if not z.shape and z0.is_infinite:
                if z.is_integer:
                    limits.append((z, Range(1, oo) if z0 > 0 else Range(-oo, 0)))
                else:
                    limits.append((z, Interval(1, oo) if z0 < 0 else Interval(-oo, -1)))

        return limits
