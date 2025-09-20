from collections import defaultdict
from functools import cmp_to_key
from .basic import Basic
from .compatibility import reduce, is_sequence
from .logic import _fuzzy_group, fuzzy_not
from .singleton import S
from .operations import AssocOp
from .cache import cacheit
from .numbers import ilcm, igcd
from .expr import Expr

# Key for sorting commutative args in canonical order
_args_sortkey = cmp_to_key(Basic.compare)


def _addsort(args):
    # in-place sorting of args
    args.sort(key=_args_sortkey)


def _unevaluated_Add(*args):
    """Return a well-formed unevaluated Add: Numbers are collected and
    put in slot 0 and args are sorted. Use this when args have changed
    but you still want to return an unevaluated Add.

    Examples
    ========

    >>> from sympy.core.add import _unevaluated_Add as uAdd
    >>> from sympy import S, Add
    >>> from sympy.abc import x, y
    >>> a = uAdd(*[S(1.0), x, S(2)])
    >>> a.args[0]
    3.00000000000000
    >>> a.args[1]
    x

    Beyond the Number being in slot 0, there is no other assurance of
    order for the arguments since they are hash sorted. So, for testing
    purposes, output produced by this in some other function can only
    be tested against the output of this function or as one of several
    options:

    >>> opts = (Add(x, y, evaluate=False), Add(y, x, evaluate=False))
    >>> a = uAdd(x, y)
    >>> assert a in opts and a == uAdd(x, y)
    >>> uAdd(x + 1, x + 2)
    x + x + 3
    """
    args = list(args)
    newargs = []
    co = S.Zero
    while args:
        a = args.pop()
        if a.is_Add:
            # this will keep nesting from building up
            # so that x + (x + 1) -> x + x + 1 (3 args)
            args.extend(a.args)
        elif a.is_Number:
            co += a
        else:
            newargs.append(a)
    _addsort(newargs)
    if co:
        newargs.insert(0, co)
    return Add._from_args(newargs)


from .decorators import _sympifyit, call_highest_priority


class Add(Expr, AssocOp):

    __slots__ = []

    identity = S.Zero
    
    @classmethod
    def flatten(cls, seq):
        """
        Takes the sequence "seq" of nested Adds and returns a flatten list.

        Returns: (commutative_part, noncommutative_part, order_symbols)

        Applies associativity, all terms are commutable with respect to
        addition.

        NB: the removal of 0 is already handled by AssocOp.__new__

        See also
        ========

        sympy.core.mul.Mul.flatten

        """
        from sympy.calculus.util import AccumBounds
#         from sympy.matrices.expressions import MatrixExpr
        from sympy.tensor.tensor import TensExpr
        rv = None
        if len(seq) == 2:
            a, b = seq
            if b.is_Rational:
                a, b = b, a
            if a.is_Rational:
                if b.is_Mul:
                    rv = [a, b], [], None
            if rv:
#                 if all(s.is_commutative for s in rv[0]):
                return rv
#                 return [], rv[0], None

        terms = {}  # term -> coeff
                        # e.g. x**2 -> 5   for ... + 5*x**2 + ...

        coeff = S.Zero  # coefficient (Number or zoo) to always be in slot 0
                        # e.g. 3 + ...
        order_factors = []

        infinitesimal = None
        from sympy import Ones, Zeros
        for i, o in enumerate(seq):

            # O(x)
            if o.is_Order:
                for o1 in order_factors:
                    if o1.contains(o):
                        o = None
                        break
                if o is None:
                    continue
                order_factors = [o] + [
                    o1 for o1 in order_factors if not o.contains(o1)]
                continue

            # 3 or NaN
            elif o.is_Number:
                if (o is S.NaN or coeff is S.ComplexInfinity and
                        o.is_finite == False):
                    # we know for sure the result will be nan
                    return [S.NaN], [], None
                if coeff.is_Number:
                    from sympy.core.numbers import Infinitesimal, NegativeInfinitesimal
                    if isinstance(o, (Infinitesimal, NegativeInfinitesimal)):
                        infinitesimal = o
                        continue
                    coeff += o
                    if coeff is S.NaN:
                        # we know for sure the result will be nan
                        return [S.NaN], [], None
                continue

            elif isinstance(o, AccumBounds):
                coeff = o.__add__(coeff)
                continue

            elif isinstance(o, TensExpr):
                coeff = o.__add__(coeff) if coeff else o
                continue

            elif o is S.ComplexInfinity:
                if coeff.is_finite == False:
                    # we know for sure the result will be nan
                    return [S.NaN], [], None
                coeff = S.ComplexInfinity
                continue

            # Add([...])
            elif o.is_Add:
                # NB: here we assume Add is always commutative
                seq.extend(o.args)  # TODO zerocopy?
                continue

            # Mul([...])
            elif o.is_Mul:
                c, s = o.as_coeff_Mul()
                if not c.shape and s.is_Ones:
                    shape = Add.broadcast_from_sequence(seq[:i] + seq[i + 1:])
                    if len(shape) >= len(s.shape):
                        s = S.One
                        
            # check for unevaluated Pow, e.g. 2**3 or 2**(-1/2)
            elif o.is_Pow:
                b, e = o.as_base_exp()
                if b.is_Number and (e.is_Integer or
                                   (e.is_Rational and e.is_negative)):
                    seq.append(b ** e)
                    continue
                c, s = S.One, o

            elif o.is_zero:
                if o.shape:
                    coeff *= Ones(*o.shape) 
                # skipping any zero values
                continue
            else:
                # everything else
                c = S.One
                s = o

            # now we have:
            # o = c*s, where
            #
            # c is a Number
            # s is an expression with number factor extracted
            # let's collect terms with the same s, so e.g.
            # 2*x**2 + 3*x**2  ->  5*x**2
            if s in terms:
                terms[s] += c
                if terms[s] is S.NaN:
                    # we know for sure the result will be nan
                    return [S.NaN], [], None
            else:
                terms[s] = c

        # now let's construct new args:
        # [2*x**2, x**3, 7*x**4, pi, ...]
        newseq = []
        noncommutative = False
        for s, c in terms.items():
            if s.is_Ones:
                if coeff.is_zero or coeff.is_infinite:
                    ...
                else:
                    c += coeff
                    coeff = S.Zero
            
            # 0*s
            if c is S.Zero:
                continue
            # 1*s
            elif c is S.One:
                
                newseq.append(s)
            # c*s
            else:
                if s.is_Mul:
                    # Mul, already keeps its arguments in perfect order.
                    # so we can simply put c in slot0 and go the fast way.
                    cs = s._new_rawargs(*((c,) + s.args))
                    newseq.append(cs)
                elif s.is_Add:
                    # we just re-create the unevaluated Mul
                    newseq.append(Mul(c, s, evaluate=False))
                else:
                    # alternatively we have to call all Mul's machinery (slow)
                    newseq.append(Mul(c, s))

        # oo, -oo
        if coeff is S.Infinity:
            newseq = [f for f in newseq if not (f.is_extended_nonnegative or f.is_real)]
            infinitesimal = None

        elif coeff is S.NegativeInfinity:
            newseq = [f for f in newseq if not (f.is_extended_nonpositive or f.is_real)]
            infinitesimal = None

        if coeff is S.ComplexInfinity:
            # zoo might be
            #   infinite_real + finite_im
            #   finite_real + infinite_im
            #   infinite_real + infinite_im
            # addition of a finite real or imaginary number won't be able to
            # change the zoo nature; adding an infinite qualtity would result
            # in a NaN condition if it had sign opposite of the infinite
            # portion of zoo, e.g., infinite_real - infinite_real.
            newseq = [c for c in newseq if not (c.is_finite and c.is_extended_real is not None)]
            infinitesimal = None

        # process O(x)
        if order_factors:
            newseq2 = []
            for t in newseq:
                for o in order_factors:
                    # x + O(x) -> O(x)
                    if o.contains(t):
                        t = None
                        break
                # x + O(x**2) -> x + O(x**2)
                if t is not None:
                    newseq2.append(t)
            newseq = newseq2 + order_factors
            # 1 + O(1) -> O(1)
            for o in order_factors:
                if o.contains(coeff):
                    coeff = S.Zero
                    break

        # order args canonically
        _addsort(newseq)

        # current code expects coeff to be first
        if not coeff.is_zero:
            newseq.insert(0, coeff)
        
        if infinitesimal is not None:
            newseq.append(infinitesimal)

        # we are done
        if noncommutative:
            return [], newseq, None

        if not newseq:
            shape = Add.broadcast_from_sequence(seq)
            if shape:
                newseq.append(Zeros(*shape))
        
        return newseq, [], None

    
    @staticmethod
    def broadcast_from_sequence(args):
        shapes = [mat.shape for mat in args if mat.shape]
        if shapes:
            Add.broadcast(shapes)
            for shape in shapes:
                if shape[0] != 1:
                    break
            if shape[0] == 1:
                shape = shape[1:]
            return shape
        return ()
    
    @staticmethod
    def broadcast(shapes):
        length = 0
        cols = 0
        for i, shape in enumerate(shapes):
            if not shape:
                shapes[i] = (1,)
                shape = shapes[i]
            if len(shape) > 2:
                ...
            else:
                if cols == 0:
                    cols = shape[-1]
                elif shape[-1] > cols:
                    cols = shape[-1]
            if len(shape) > length:
                length = len(shape)
                
        if length == 1 and all(shape[0] == shapes[0][0] and len(shape) == length for shape in shapes): 
            length += 1
            
        for i, shape in enumerate(shapes):
            if len(shape) > 2:
                ...
            else:
                if shape[-1] < cols and len(shape) > 1:
                    shape = shape[:-1] + (cols,)
            if len(shape) < length:
                shape = (1,) * (length - len(shape)) + shape
            shapes[i] = shape
        return shapes
    
    @classmethod
    def class_key(cls):
        """Nice order of classes"""
        return 3, 1, cls.__name__

    @property
    def kind(self):
        k = attrgetter('kind')
        kinds = map(k, self.args)
        kinds = frozenset(kinds)
        if len(kinds) != 1:
            # Since addition is group operator, kind must be same.
            # We know that this is unexpected signature, so return this.
            result = UndefinedKind
        else:
            result, = kinds
        return result

    def as_coefficients_dict(a):
        """Return a dictionary mapping terms to their Rational coefficient.
        Since the dictionary is a defaultdict, inquiries about terms which
        were not present will return a coefficient of 0. If an expression is
        not an Add it is considered to have a single term.

        Examples
        ========

        >>> from sympy.abc import a, x
        >>> (3*x + a*x + 4).as_coefficients_dict()
        {1: 4, x: 3, a*x: 1}
        >>> _[a]
        0
        >>> (3*a*x).as_coefficients_dict()
        {a*x: 3}
        """

        d = defaultdict(list)
        for ai in self.args:
            c, m = ai.as_coeff_Mul()
            d[m].append(c)
        for k, v in d.items():
            if len(v) == 1:
                d[k] = v[0]
            else:
                d[k] = Add(*v)
        di = defaultdict(int)
        di.update(d)
        return di

    @cacheit
    def as_coeff_add(self, *deps):
        """
        Returns a tuple (coeff, args) where self is treated as an Add and coeff
        is the Number term and args is a tuple of all other terms.

        Examples
        ========

        >>> from sympy.abc import x
        >>> (7 + 3*x).as_coeff_add()
        (7, (3*x,))
        >>> (7*x).as_coeff_add()
        (0, (7*x,))
        """
        if deps:
            l1 = []
            l2 = []
            for f in self.args:
                if f.has(*deps):
                    l2.append(f)
                else:
                    l1.append(f)
            return self._new_rawargs(*l1), tuple(l2)
        coeff, notrat = self.args[0].as_coeff_add()
        if coeff is not S.Zero:
            return coeff, notrat + self.args[1:]
        return S.Zero, self.args

    def as_coeff_Add(self, rational=False):
        """Efficiently extract the coefficient of a summation. """
        coeff, args = self.args[0], self.args[1:]

        if coeff.is_Number and not rational or coeff.is_Rational:
            return coeff, self._new_rawargs(*args)
        return S.Zero, self

    # Note, we intentionally do not implement Add.as_coeff_mul().  Rather, we
    # let Expr.as_coeff_mul() just always return (S.One, self) for an Add.  See
    # issue 5524.

    def _eval_power(self, e):
        if e.is_Rational and self.is_number:
            from sympy.core.evalf import pure_complex
            from sympy.core.mul import _unevaluated_Mul
            from sympy.core.exprtools import factor_terms
            from sympy.core.function import expand_multinomial
            from sympy.functions.elementary.complexes import sign
            from sympy.core.power import sqrt
            ri = pure_complex(self)
            if ri:
                r, i = ri
                if e.q == 2:
                    D = sqrt(r ** 2 + i ** 2)
                    if D.is_Rational:
                        # (r, i, D) is a Pythagorean triple
                        root = sqrt(factor_terms((D - r) / 2)) ** e.p
                        return root * expand_multinomial((
                            # principle value
                            (D + r) / abs(i) + sign(i) * S.ImaginaryUnit) ** e.p)
                elif e == -1:
                    return _unevaluated_Mul(
                        r - i * S.ImaginaryUnit,
                        1 / (r ** 2 + i ** 2))

    def _eval_exp(self):
        from sympy import exp
        out = []
        add = []
        for a in self.args:
            if a is S.One:
                add.append(a)
                continue
            newa = exp(a)
            if isinstance(newa, exp):
                add.append(a)
            else:
                out.append(newa)
        if out:
            return Mul(*out) * exp(Add(*add), evaluate=False)
        
    @cacheit
    def _eval_derivative(self, s):
        return self.func(*[a.diff(s) for a in self.args])

    def _eval_nseries(self, x, n, logx):
        terms = [t.nseries(x, n=n, logx=logx) for t in self.args]
        return self.func(*terms)

    def _matches_simple(self, expr, repl_dict):
        # handle (w+3).matches('x+5') -> {w: x+2}
        coeff, terms = self.as_coeff_add()
        if len(terms) == 1:
            return terms[0].matches(expr - coeff, repl_dict)
        return

    def matches(self, expr, repl_dict={}, old=False):
        return AssocOp._matches_commutative(self, expr, repl_dict, old)

    @staticmethod
    def _combine_inverse(lhs, rhs):
        """
        Returns lhs - rhs, but treats oo like a symbol so oo - oo
        returns 0, instead of a nan.
        """
        from sympy.core.function import expand_mul
        from sympy.core.symbol import Dummy
        inf = (S.Infinity, S.NegativeInfinity)
        if lhs.has(*inf) or rhs.has(*inf):
            oo = Dummy('oo')
            reps = {
                S.Infinity: oo,
                S.NegativeInfinity:-oo}
            ireps = {v: k for k, v in reps.items()}
            eq = expand_mul(lhs.xreplace(reps) - rhs.xreplace(reps))
            if eq.has(oo):
                eq = eq.replace(
                    lambda x: x.is_Pow and x.base == oo,
                    lambda x: x.base)
            return eq.xreplace(ireps)
        else:
            return expand_mul(lhs - rhs)

    @cacheit
    def as_two_terms(self):
        """Return head and tail of self.

        This is the most efficient way to get the head and tail of an
        expression.

        - if you want only the head, use self.args[0];
        - if you want to process the arguments of the tail then use
          self.as_coef_add() which gives the head and a tuple containing
          the arguments of the tail when treated as an Add.
        - if you want the coefficient when self is treated as a Mul
          then use self.as_coeff_mul()[0]

        >>> from sympy.abc import x, y
        >>> (3*x - 2*y + 5).as_two_terms()
        (5, 3*x - 2*y)
        """
        return self.args[0], self._new_rawargs(*self.args[1:])

    def as_numer_denom(self):

        # clear rational denominator
        content, expr = self.primitive()
        ncon, dcon = content.as_numer_denom()

        # collect numerators and denominators of the terms
        nd = defaultdict(list)
        for f in expr.args:
            ni, di = f.as_numer_denom()
            nd[di].append(ni)

        # check for quick exit
        if len(nd) == 1:
            d, n = nd.popitem()
            return self.func(
                *[_keep_coeff(ncon, ni) for ni in n]), _keep_coeff(dcon, d)

        # sum up the terms having a common denominator
        for d, n in nd.items():
            if len(n) == 1:
                nd[d] = n[0]
            else:
                nd[d] = self.func(*n)

        # assemble single numerator and denominator
        denoms, numers = [list(i) for i in zip(*iter(nd.items()))]
        n, d = self.func(*[Mul(*(denoms[:i] + [numers[i]] + denoms[i + 1:]))
                   for i in range(len(numers))]), Mul(*denoms)

        return _keep_coeff(ncon, n), _keep_coeff(dcon, d)

    def _eval_is_polynomial(self, syms):
        return all(term._eval_is_polynomial(syms) for term in self.args)

    def _eval_is_rational_function(self, syms):
        return all(term._eval_is_rational_function(syms) for term in self.args)

    def _eval_is_algebraic_expr(self, syms):
        return all(term._eval_is_algebraic_expr(syms) for term in self.args)

    # assumption methods
    _eval_is_antihermitian = lambda self: _fuzzy_group((a.is_antihermitian for a in self.args), quick_exit=True)
    _eval_is_hermitian = lambda self: _fuzzy_group((a.is_hermitian for a in self.args), quick_exit=True)    
    _eval_is_algebraic = lambda self: _fuzzy_group((a.is_algebraic for a in self.args), quick_exit=True)
    
    def _eval_is_finite(self):
        from sympy.core.logic import fuzzy_and
        return fuzzy_and((a.is_finite for a in self.args))
    
    def _eval_is_extended_integer(self):
        nonintegers = []
        pieces = []
        for arg in self.args:
            integer = arg.is_extended_integer
            if integer is None:
                return
            if integer:
                continue
            
            if arg.is_Piecewise:
                pieces.append(arg)
            else:
                nonintegers.append(arg)    

        if len(pieces) > 1:
            return
        
        if pieces:
            piece, = pieces
            if nonintegers:
                self = self.func(*nonintegers)
                piece = piece.func(*((e + self, c) for e, c in piece.args))

            return piece.is_extended_integer

        if not nonintegers:
            return True

        if len(nonintegers) < len(self.args):
            self = self.func(*nonintegers)
        num, den = self.as_numer_denom()
        if den.is_extended_integer:
            rem = num % den
            if rem.is_zero:
                return True
            if rem.is_zero is None:
                return
            return False
        if den.is_extended_integer is None:
            return
        if num.is_extended_integer:
            return False
                
    def _eval_is_super_integer(self):
        return _fuzzy_group((a.is_super_integer for a in self.args), quick_exit=True)
    
    def _eval_is_extended_rational(self):
        return _fuzzy_group((a.is_extended_rational for a in self.args), quick_exit=True)
    
    def _eval_is_hyper_rational(self):
        return _fuzzy_group((a.is_hyper_rational for a in self.args), quick_exit=True)
    
    def _eval_is_super_rational(self):
        return _fuzzy_group((a.is_super_rational for a in self.args), quick_exit=True)
    
    def _eval_is_extended_real(self):
        return _fuzzy_group((a.is_extended_real for a in self.args), quick_exit=True)
        
    def _eval_is_hyper_real(self):
        return _fuzzy_group((a.is_hyper_real for a in self.args), quick_exit=True)
    
    def _eval_is_super_real(self):
        return _fuzzy_group((a.is_super_real for a in self.args), quick_exit=True)
    
    def _eval_is_extended_complex(self):
        return _fuzzy_group((a.is_extended_complex for a in self.args), quick_exit=True)
                
    def _eval_is_hyper_complex(self):
        return _fuzzy_group((a.is_hyper_complex for a in self.args), quick_exit=True)
    
    def _eval_is_imaginary(self):
        nz = []
        im_I = []
        for a in self.args:
            if a.is_extended_real:
                if a.is_zero:
                    pass
                elif a.is_zero == False:
                    nz.append(a)
                else:
                    return
            elif a.is_imaginary:
                im_I.append(a * S.ImaginaryUnit)
            elif (S.ImaginaryUnit * a).is_extended_real:
                im_I.append(a * S.ImaginaryUnit)
            else:
                return
        b = self.func(*nz)
        if b.is_zero:
            return fuzzy_not(self.func(*im_I).is_zero)
        elif b.is_zero == False:
            return False

    def _eval_is_nonzero(self):
        if self.shape:
            if all(arg.is_extended_positive for arg in self.args):
                return True
                
            if all(arg.is_extended_negative for arg in self.args):
                return True
            
        if self.is_odd:
            return True

        return super(Add, self)._eval_is_nonzero()
         
    def _eval_is_zero(self):
        if self.shape:
            if all(arg.is_extended_positive for arg in self.args):
                return False
                
            if all(arg.is_extended_negative for arg in self.args):
                return False
            
            return
        
        if len(self.args) == 2:
            if self.is_extended_real:
                if self.min().is_extended_positive:
                    return False
                if self.max().is_extended_negative:
                    return False

    def _eval_is_irrational(self):
        for t in self.args:
            a = t.is_irrational
            if a:
                others = list(self.args)
                others.remove(t)
                if all(x.is_rational == True for x in others):
                    return True
                return None
            if a is None:
                return
        return False
    
    def _eval_is_extended_positive(self):
        infinitesimality = self.infinitesimality
        if infinitesimality is True:
            return self.clear_infinitesimal()[0].is_extended_nonnegative
        elif infinitesimality is False:
            return self.clear_infinitesimal()[0].is_extended_positive
        
        if self.is_number:
            return Expr._eval_is_extended_positive(self)
        
        f = self.min()
        if f is not self and f.is_extended_positive:
            return True
        f = self.max()
        if f is not self and f.is_extended_nonpositive:
            return False
        
        if all(arg.is_extended_nonnegative for arg in self.args):
            if any(arg.is_extended_positive for arg in self.args):
                return True
            
        if all(arg.is_extended_nonpositive for arg in self.args):
            return False
    
    def _eval_is_extended_negative(self):
        infinitesimality = self.infinitesimality
        if infinitesimality is True:
            return self.clear_infinitesimal()[0].is_extended_negative
        elif infinitesimality is False:
            return self.clear_infinitesimal()[0].is_extended_nonpositive
            
        if self.is_number: 
            return Expr._eval_is_extended_negative(self)
        
        f = self.max()
        if f is not self and f.is_extended_negative:
            return True
        f = self.min()
        if f is not self and f.is_extended_nonnegative:
            return False
        
        if all(arg.is_extended_nonpositive for arg in self.args):
            if any(arg.is_extended_negative for arg in self.args):
                return True

        if all(arg.is_extended_nonnegative for arg in self.args):
            return False

    def _eval_subs(self, old, new, **hint):
        if not old.is_Add:
            if old is S.Infinity and -old in self.args:
                # foo - oo is foo + (-oo) internally
                return self.xreplace({-old:-new})
            return

        coeff_self, terms_self = self.as_coeff_Add()
        coeff_old, terms_old = old.as_coeff_Add()

        if coeff_self.is_Rational and coeff_old.is_Rational:
            if terms_self == terms_old:  # (2 + a).subs( 3 + a, y) -> -1 + y
                return self.func(new, coeff_self, -coeff_old)
            if terms_self == -terms_old:  # (2 + a).subs(-3 - a, y) -> -1 - y
                return self.func(-new, coeff_self, coeff_old)

        if coeff_self.is_Rational and coeff_old.is_Rational \
                or coeff_self == coeff_old:
            args_old, args_self = self.func.make_args(
                terms_old), self.func.make_args(terms_self)
            if len(args_old) < len(args_self):  # (a+b+c).subs(b+c,x) -> a+x
                self_set = set(args_self)
                old_set = set(args_old)

                if old_set < self_set:
                    ret_set = self_set - old_set
                    return self.func(new, coeff_self, -coeff_old,
                               *[s._subs(old, new, **hint) for s in ret_set])

                args_old = self.func.make_args(
                    -terms_old)  # (a+b+c+d).subs(-b-c,x) -> a-x+d
                old_set = set(args_old)
                if old_set < self_set:
                    ret_set = self_set - old_set
                    return self.func(-new, coeff_self, coeff_old,
                               *[s._subs(old, new, **hint) for s in ret_set])

    def removeO(self):
        args = [a for a in self.args if not a.is_Order]
        return self._new_rawargs(*args)

    def getO(self):
        args = [a for a in self.args if a.is_Order]
        if args:
            return self._new_rawargs(*args)

    @cacheit
    def extract_leading_order(self, symbols, point=None):
        """
        Returns the leading term and its order.

        Examples
        ========

        >>> from sympy.abc import x
        >>> (x + 1 + 1/x**5).extract_leading_order(x)
        ((x**(-5), O(x**(-5))),)
        >>> (1 + x).extract_leading_order(x)
        ((1, O(1)),)
        >>> (x + x**2).extract_leading_order(x)
        ((x, O(x)),)

        """
        from sympy import Order
        lst = []
        symbols = list(symbols if is_sequence(symbols) else [symbols])
        if not point:
            point = [0] * len(symbols)
        seq = [(f, Order(f, *zip(symbols, point))) for f in self.args]
        for ef, of in seq:
            for e, o in lst:
                if o.contains(of) and o != of:
                    of = None
                    break
            if of is None:
                continue
            new_lst = [(ef, of)]
            for e, o in lst:
                if of.contains(o) and o != of:
                    continue
                new_lst.append((e, o))
            lst = new_lst
        return tuple(lst)

    def as_real_imag(self, deep=True, **_):
        """
        returns a tuple representing a complex number

        Examples
        ========

        >>> from sympy import I
        >>> (7 + 9*I).as_real_imag()
        (7, 9)
        >>> ((1 + I)/(1 - I)).as_real_imag()
        (0, 1)
        >>> ((1 + 2*I)*(1 + 3*I)).as_real_imag()
        (-5, 5)
        """
        sargs = self.args
        re_part, im_part = [], []
        for term in sargs:
            re, im = term.as_real_imag(deep=deep)
            re_part.append(re)
            im_part.append(im)
        return self.func(*re_part), self.func(*im_part)

    def _eval_as_leading_term(self, x, cdir=0):
        from sympy import expand_mul, factor_terms

        old = self

        expr = expand_mul(self)
        if not expr.is_Add:
            return expr.as_leading_term(x, cdir=cdir)

        infinite = [t for t in expr.args if t.is_infinite]

        expr = expr.func(*[t.as_leading_term(x) for t in expr.args]).removeO()
        if not expr:
            # simple leading term analysis gave us 0 but we have to send
            # back a term, so compute the leading term (via series)
            return old.compute_leading_term(x)
        elif expr is S.NaN:
            return old.func._from_args(infinite)
        elif not expr.is_Add:
            return expr
        else:
            plain = expr.func(*[s for s, _ in expr.extract_leading_order(x)])
            rv = factor_terms(plain, fraction=False)
            from sympy.simplify import simplify
            rv_simplify = simplify(rv)
            # if it simplifies to an x-free expression, return that;
            # tests don't fail if we don't but it seems nicer to do this
            if x not in rv_simplify.free_symbols:
                if rv_simplify.is_zero and plain.is_zero is not True:
                    return (expr - plain)._eval_as_leading_term(x)
                return rv_simplify
            return rv

    def _eval_adjoint(self):
        return self.func(*(t.adjoint() for t in self.args))

    def _eval_conjugate(self):
        return self.func(*(t.conjugate() for t in self.args))

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            scalar = []
            vector = []
            matrix = []
            for arg in self.args:
                if not arg.shape:
                    scalar.append(arg)
                elif len(arg.shape) == 1:
                    vector.append(arg)
                else:
                    matrix.append(arg)
                
            if not vector:
                return self.func(*(arg.T for arg in self.args))

            from sympy import Ones
            one = Ones(*self.shape)
            vector = [v * one for v in vector]
            matrix += vector

            matrix = self.func(*(arg.T for arg in matrix))
            if scalar:
                matrix += self.func(*scalar)

            return matrix

    def __neg__(self):
        return self * (-1)

    def primitive(self):
        """
        Return ``(R, self/R)`` where ``R``` is the Rational GCD of ``self```.

        ``R`` is collected only from the leading coefficient of each term.

        Examples
        ========

        >>> from sympy.abc import x, y

        >>> (2*x + 4*y).primitive()
        (2, x + 2*y)

        >>> (2*x/3 + 4*y/9).primitive()
        (2/9, 3*x + 2*y)

        >>> (2*x/3 + 4.2*y).primitive()
        (1/3, 2*x + 12.6*y)

        No subprocessing of term factors is performed:

        >>> ((2 + 2*x)*x + 2).primitive()
        (1, x*(2*x + 2) + 2)

        Recursive processing can be done with the ``as_content_primitive()``
        method:

        >>> ((2 + 2*x)*x + 2).as_content_primitive()
        (2, x*(x + 1) + 1)

        See also: primitive() function in polytools.py

        """

        terms = []
        inf = False
        for a in self.args:
            c, m = a.as_coeff_Mul()
            if not c.is_Rational:
                c = S.One
                m = a
            inf = inf or m is S.ComplexInfinity
            terms.append((c.p, c.q, m))

        if not inf:
            ngcd = reduce(igcd, [t[0] for t in terms], 0)
            dlcm = reduce(ilcm, [t[1] for t in terms], 1)
        else:
            ngcd = reduce(igcd, [t[0] for t in terms if t[1]], 0)
            dlcm = reduce(ilcm, [t[1] for t in terms if t[1]], 1)

        if ngcd == dlcm == 1:
            return S.One, self
        if not inf:
            for i, (p, q, term) in enumerate(terms):
                terms[i] = _keep_coeff(Rational((p // ngcd) * (dlcm // q)), term)
        else:
            for i, (p, q, term) in enumerate(terms):
                if q:
                    terms[i] = _keep_coeff(Rational((p // ngcd) * (dlcm // q)), term)
                else:
                    terms[i] = _keep_coeff(Rational(p, q), term)

        # we don't need a complete re-flattening since no new terms will join
        # so we just use the same sort as is used in Add.flatten. When the
        # coefficient changes, the ordering of terms may change, e.g.
        #     (3*x, 6*y) -> (2*y, x)
        #
        # We do need to make sure that term[0] stays in position 0, however.
        #
        if terms[0].is_Number or terms[0] is S.ComplexInfinity:
            c = terms.pop(0)
        else:
            c = None
        _addsort(terms)
        if c:
            terms.insert(0, c)
        return Rational(ngcd, dlcm), self._new_rawargs(*terms)

    def as_content_primitive(self, radical=False, clear=True):
        """Return the tuple (R, self/R) where R is the positive Rational
        extracted from self. If radical is True (default is False) then
        common radicals will be removed and included as a factor of the
        primitive expression.

        Examples
        ========

        >>> from sympy import sqrt
        >>> (3 + 3*sqrt(2)).as_content_primitive()
        (3, 1 + sqrt(2))

        Radical content can also be factored out of the primitive:

        >>> (2*sqrt(2) + 4*sqrt(10)).as_content_primitive(radical=True)
        (2, sqrt(2)*(1 + 2*sqrt(5)))

        See docstring of Expr.as_content_primitive for more examples.
        """
        con, prim = self.func(*[_keep_coeff(*a.as_content_primitive(
            radical=radical, clear=clear)) for a in self.args]).primitive()
        if not clear and not con.is_Integer and prim.is_Add:
            con, d = con.as_numer_denom()
            _p = prim / d
            if any(a.as_coeff_Mul()[0].is_Integer for a in _p.args):
                prim = _p
            else:
                con /= d
        if radical and prim.is_Add:
            # look for common radicals that can be removed
            args = prim.args
            rads = []
            common_q = None
            for m in args:
                term_rads = defaultdict(list)
                for ai in Mul.make_args(m):
                    if ai.is_Pow:
                        b, e = ai.as_base_exp()
                        if e.is_Rational and b.is_Integer:
                            term_rads[e.q].append(abs(int(b)) ** e.p)
                if not term_rads:
                    break
                if common_q is None:
                    common_q = set(term_rads.keys())
                else:
                    common_q = common_q & set(term_rads.keys())
                    if not common_q:
                        break
                rads.append(term_rads)
            else:
                # process rads
                # keep only those in common_q
                for r in rads:
                    for q in list(r.keys()):
                        if q not in common_q:
                            r.pop(q)
                    for q in r:
                        r[q] = prod(r[q])
                # find the gcd of bases for each q
                G = []
                for q in common_q:
                    g = reduce(igcd, [r[q] for r in rads], 0)
                    if g != 1:
                        G.append(g ** Rational(1, q))
                if G:
                    G = Mul(*G)
                    args = [ai / G for ai in args]
                    prim = G * prim.func(*args)

        return con, prim

    @property
    def _sorted_args(self):
        from sympy.core.compatibility import default_sort_key
        return tuple(sorted(self.args, key=default_sort_key))

    def _eval_difference_delta(self, n, step):
        from sympy.series.limitseq import difference_delta as dd
        return self.func(*[dd(a, n, step) for a in self.args])

    @property
    def _mpc_(self):
        """
        Convert self to an mpmath mpc if possible
        """
        from sympy.core.numbers import I, Float
        re_part, rest = self.as_coeff_Add()
        im_part, imag_unit = rest.as_coeff_Mul()
        if not imag_unit == I:
            # ValueError may seem more reasonable but since it's a @property,
            # we need to use AttributeError to keep from confusing things like
            # hasattr.
            raise AttributeError("Cannot convert Add to mpc. Must be of the form Number + Number*I")

        return (Float(re_part)._mpf_, Float(im_part)._mpf_)

    def enumerate_KroneckerDelta(self):
        for arg in self.args:
            yield from arg.enumerate_KroneckerDelta()

    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a Add object!
        """
        if rhs.is_Add:
            lhs_args = [*lhs.args]
            rhs_args = [*rhs.args]
            intersect = set(lhs_args) & set(rhs_args)
            if intersect:
                for arg in intersect:
                    lhs_args.remove(arg)
                    rhs_args.remove(arg)
                return self.func(cls(*lhs_args), cls(*rhs_args)).simplify()

        elif rhs in lhs.args:
            args = [*lhs.args]
            args.remove(rhs)
            return self.func(cls(*args), 0).simplify()
        elif rhs.is_zero:
            return Basic.simplify_Equal(self, lhs, rhs)
            
    @classmethod
    def simplify_Relational(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a Add object!
        """
        if rhs.is_Add:
            lhs_args = [*lhs.args]
            rhs_args = [*rhs.args]
            intersect = set(lhs_args) & set(rhs_args)
            if intersect:
                hit = False
                for arg in intersect:
                    if arg.is_real:
                        lhs_args.remove(arg)
                        rhs_args.remove(arg)
                        hit = True
                if hit:
                    return self.func(cls(*lhs_args), cls(*rhs_args)).simplify()

        elif rhs in lhs.args:
            args = [*lhs.args]
            args.remove(rhs)
            return self.func(cls(*args), 0).simplify()
        elif rhs.is_zero:
            return Basic.simplify_Relational(self, lhs, rhs)
        
    @classmethod
    def simplify_Unequal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a Add object!
        """
        if len(lhs.args) == 2:
            if rhs.is_zero:
                lhs, rhs = lhs.args
                if lhs._coeff_isneg():
                    rhs, lhs = -lhs, rhs
                    return self.func(lhs, rhs).simplify()
                if rhs._coeff_isneg():
                    rhs = -rhs
                    return self.func(lhs, rhs).simplify()

    def simplify_KroneckerDelta(self): 
        dic = {}
       
        for expr in self.enumerate_KroneckerDelta():
            if expr not in dic:
                dic[expr] = 0
            dic[expr] += 1
        
        dic = {key: value for key, value in dic.items() if value > 1}
            
        if not dic:
            return self
        
        this = self
        for delta in dic:
            p = this.as_poly(delta)
            if p is None:
                continue
            degree = p.degree()
            if degree < 0:
                continue
            
            if degree == 0:
#                 for simplification purposes only
                constant = p.nth(0)
                if not constant._has(delta):
                    this = constant
                continue
                
            coefficient = p.nth(1)
            for d in range(2, degree + 1):
                coefficient += p.nth(d)

            i, j = delta.args
            _coefficient = coefficient._subs(j, i, symbol=False)
            if _coefficient == coefficient:
                __coefficient = coefficient._subs(i, j)
                if __coefficient.is_zero:
                    _coefficient = __coefficient
                
            if _coefficient == coefficient:
                if degree == 1:
                    continue
            else:
                coefficient = _coefficient
                if coefficient.is_Add:
                    coefficient = coefficient.simplify_KroneckerDelta()     
                        
            this = coefficient * delta + p.nth(0)
            if this.is_Add:
                this = this.simplify_KroneckerDelta()
            
        return this

    def simplify(self, deep=False, **kwargs):
        if deep:
            this = Expr.simplify(self, deep=True, **kwargs)
            if this is not self:
                return this
            
        for i, arg in enumerate(self.args):
            if arg.is_Stack:
                _arg = arg.simplify(squeeze=True)
                if _arg != arg:
                    args = [*self.args]
                    args[i] = _arg
                    return self.func(*args).simplify()

        this = self.simplifyPiecewise()
        if this is not self:
            if deep:
                return this.simplify(deep=deep)
            return this

        this = self.simplify_KroneckerDelta()
        if this != self:
            return this

        this = self.simplifySummations()
        if this is not self:
            return this
        
        this = self.simplifyMatrix()
        if this is not self:
            return this

        this = self.simplify_OneMatrix()
        if this is not self:
            return this
        
        return self
            
    def simplifyPiecewise(self): 
        piecewise = [arg for arg in self.args if arg.is_Piecewise]
        if not piecewise:
            return self
        
        if len(piecewise) == 1:
            return self
                 
        for i in range(1, len(piecewise)):
            new = piecewise[i - 1].try_add(piecewise[i])
            if new is not None:
                args = [*self.args]
                args.remove(piecewise[i - 1])
                args.remove(piecewise[i])
                args.append(new)
                return self.func(*args, evaluate=False).simplify()
        
        return self
    
    def simplifyMatrix(self): 
        matrix = [arg for arg in self.args if arg.is_DenseMatrix]
        scalar = [arg for arg in self.args if not arg.shape]
        if not matrix or not scalar:
            return self
        
        return self.func(*matrix) + self.func(*scalar)
    
    def simplify_OneMatrix(self): 
        max_len = self.max_len_shape()
        
        for i, times in enumerate(self.args):
            if times.is_Mul and any(t.is_Ones for t in times.args):
                if len(times.shape) < max_len or \
                len(times.shape) == max_len and max_len == max(len(arg.shape) for j, arg in enumerate(self.args) if j != i):
                    args = [*self.args]
                    args[i] = times.squeeze()
                    return self.func(*args).simplify()
                                    
        return self
    
    def simplifySummations(self):
        from sympy.concrete.summations import Sum
        from sympy import Wild
        dic = {}
        ceoffs = []
        for arg in self.args:

            if isinstance(arg, Sum):
                if arg.expr._coeff_isneg():
                    arg = arg.func(-arg.expr, *arg.limits)
                    key = S.NegativeOne
                else:
                    key = S.One
                    
                if key in dic:
                    dic[key].append(arg)
                else:
                    dic[key] = [arg]
                continue

            coeff, summation = arg.as_coeff_Sum()
            if coeff is None:
                ceoffs.append(arg)
                continue

            if coeff in dic:
                dic[coeff].append(summation)
            else:
                dic[coeff] = [summation]

        if not dic:
            positiveInfinity = False
            negativeInfinity = False
            for arg in self.args:
                if arg == S.Infinity:
                    positiveInfinity = True
                if arg == S.NegativeInfinity:
                    negativeInfinity = True

            if negativeInfinity:
                if positiveInfinity:
                    return self
                return S.NegativeInfinity
            if positiveInfinity:
                return S.Infinity

            return self

        hit = False
        for coeff in dic:
            if -coeff not in dic:
                continue
            if coeff._coeff_isneg():
                continue

            positive = dic[coeff]
            negative = dic[-coeff]

            for index, pos in enumerate(positive):
                if not pos.limits:
                    continue
                t = pos.limits[0][0]
                if t.shape:
                    continue
                pattern = pos.expr._subs(t, Wild(t.name, **t.assumptions0), symbol=False)
                for i, neg in enumerate(negative):
                    if not (len(pos.limits) == len(neg.limits) == 1 and len(pos.limits[0]) == len(neg.limits[0]) == 3):
                        continue
                    res = neg.expr.match(pattern)
                    if not res:
                        continue

                    t_, *_ = res.values()
                    
                    (x, a, b), *_ = neg.limits
                    if not t_.is_Symbol:
                        p = t_.as_poly(x)
                        alpha = p.nth(1)
                        if alpha == S.One:
                            diff = t_ - x
                            a += diff
                            b += diff
                        elif alpha == S.NegativeOne:
                            bound = t_ + x + 1
                            a, b = bound - b, bound - a
                        else:
                            continue
                    
                    neg = Sum[t:a:b](pos.expr)
                    
                    try_sub = pos.try_sub(neg)
                    if try_sub is not None:
                        positive[index] = try_sub
                        del negative[i]
                        hit = True
                        break

        for coeff in dic:
            if self.sum_result(dic[coeff]):
                hit = True

        if hit:
            arr = []
            for coeff, expr in dic.items():
                arr += [n * coeff for n in expr]
            return Add(*arr + ceoffs).simplify()
        
        return self

    def sum_result(self, positive):
        from sympy.concrete.expr_with_limits import limits_empty
        for i in range(len(positive)):
            for j in range(i + 1, len(positive)):
                if not positive[i].is_Sum or not positive[j].is_Sum:
                    continue
                if positive[i].expr == positive[j].expr:
                    limits = positive[i].limits_intersect(positive[j])
                    if not limits_empty(limits):
                        if positive[i].limits == positive[j].limits:
                            positive[i] *= 2
                            del positive[j]
                            return True
                        continue
                    limits = positive[i].limits_union(positive[j])
                    positive[i] = positive[i].func(positive[i].expr, *limits)
                    del positive[j]
                    return True

    @property
    def domain(self):
        domain = None
        coeff = []
        for arg in self.args:
            if arg.is_number:
                coeff.append(arg)
                continue
            if domain is None:
                domain = arg.domain
            else:
                domain += arg.domain
        if coeff:
            if domain is None:
                if self.is_extended_real:
                    from sympy import Reals
                    return Reals
                else: 
                    return S.Complexes
            return domain + Add(*coeff)
        return domain

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rdiv__')
    def __div__(self, other):
        if self.infinitesimality is not None:
            return self.func(*self.args[:-1]) / other + self.args[-1] / other

        return Expr.__div__(self, other)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rmul__')
    def __mul__(self, other):
        if self.infinitesimality is not None:
            return self.func(*self.args[:-1]) * other + self.args[-1] * other

        return Expr.__mul__(self, other)

    def _eval_is_even(self):
        even = True
        for arg in self.args:
            is_even = arg.is_even
            if is_even:
                continue
            if is_even == False:
                even = not even
                continue
            return
        return even

    @property
    def infinitesimality(self):
        if self.args[-1].is_Infinitesimal:
            return True
        if self.args[-1].is_NegativeInfinitesimal:
            return False

    def clear_infinitesimal(self):
        if self.infinitesimality is None:
            return super().clear_infinitesimal()

        return self.func(*self.args[:-1]), self.args[-1]        

    def __iter__(self):
        raise TypeError

    __getitem__ = AssocOp.getitem

    def _latex(self, p, order=None):
        if p.order == 'none':
            terms = list(self.args)
        else:
            terms = p._as_ordered_terms(self, order=order)

        terms = sorted(terms, key=lambda term: term._coeff_isneg())
        
        tex = ""
        for i, term in enumerate(terms):
            if i == 0:
                pass
            else:
                if i == len(terms) - 1 and term.is_infinitesimal and len(terms) == 2:
                    first = terms[0]
                    if first.is_Mul or first.is_ExprWithLimits:
                        ...
                    else:
                        tex = "%s^%s" % (tex, '+' if term.is_Infinitesimal else '-')
                        break

                if term._coeff_isneg():
                    tex += " - "
                    term = -term
                else:
                    tex += " + "
            term_tex = p._print(term)
            if p._needs_add_brackets(term):
                term_tex = r"\left(%s\right)" % term_tex
            tex += term_tex

        return tex

    def _sympystr(self, p, order=None):
        if p.order == 'none':
            terms = [*self.args]
        else:
            terms = p._as_ordered_terms(self, order=order)

        from sympy.printing.precedence import precedence
        PREC = precedence(self)
        l = []
        for term in terms:
            t = p._print(term)
            if t.startswith('-'):
                sign = "-"
                t = t[1:]
            else:
                sign = "+"
            if precedence(term) < PREC:
                l.extend([sign, "(%s)" % t])
            else:
                l.extend([sign, t])
        sign = l.pop(0)
        if sign == '+':
            sign = ""
        return sign + ' '.join(l)

    def _lean(self, p, order=None):
        if p.order == 'none':
            terms = [*self.args]
        else:
            terms = p._as_ordered_terms(self, order=order)

        from sympy.printing.precedence import precedence
        PREC = precedence(self)
        l = []
        for term in terms:
            t = p._print(term)
            if t.startswith('-'):
                sign = "-"
                t = t[1:]
            else:
                sign = "+"
            if precedence(term) < PREC:
                l.extend([sign, "(%s)" % t])
            else:
                l.extend([sign, t])
        sign = l.pop(0)
        if sign == '+':
            sign = ""
        return sign + ' '.join(l)

    def _eval_determinant(self, **kwargs):
        if self.is_upper or self.is_lower:
            from sympy.concrete.products import Product
            i = self.generate_var(integer=True)
            n = self.shape[-2]
            return Product[i:n](self[i, i].simplify()).doit()

    @property
    def is_lower(self):
        for arg in self.args:
            if not arg.shape:
                return False
            if len(arg.shape) == 1:
                return False
            if arg.is_lower:
                continue
            return False
        return True
             
    @property
    def is_upper(self):
        for arg in self.args:
            if not arg.shape:
                return False
            if len(arg.shape) == 1:
                return False
            if arg.is_upper:
                continue
            return False
        return True

    def _eval_Abs(self):
        if all(arg.is_nonnegative for arg in self.args):
            return self
        
        if self.has(S.Infinity, S.NegativeInfinity):
            if any(a.is_infinite for a in self.as_real_imag()):
                return S.Infinity
            
        conj = ~self
        from sympy import Conjugate, Abs
        new_conj = conj.atoms(Conjugate) - self.atoms(Conjugate)
        if new_conj or self in (conj, -conj):
            return Abs(self, evaluate=False)
        
        return (self * conj).expand(power_base=False, power_exp=False, log=False, multinomial=False, basic=False) ** S.Half
        
    def of(self, cls, **kwargs):
        from sympy.core.of import Basic
        if isinstance(cls, Basic):
            indices = kwargs.get('indices', [None] * len(cls.args))
            res = Expr.of(self, cls, indices=indices)
        else:
            res = Expr.of(self, cls)
            indices = []

        if res is None:
            if cls.is_Add:
                res = self.rotary_match(cls, indices)

            elif cls.is_Mul:
                args = []
                common_terms = set()
                for arg in self.args:
                    if ac := arg.of(cls):
                        a, c = ac
                        args.append(a)
                        common_terms.add(c)
                        if len(common_terms) > 1:
                            return
                    else:
                        return
                c, = common_terms
                return Add(*args), c
                    
        if isinstance(res, tuple) and isinstance(cls, Basic):
            if len(res) > 2:
                if cls.of_subtraction_pattern():
                    negative = []
                    positive = []
                    for arg in self.args:
                        if arg._coeff_isneg():
                            negative.append(-arg)
                        else:
                            positive.append(arg)
                    
                    return Add(*positive), Add(*negative)

                elif cls.of_two_terms():
                    *res, mul = res
                    return Add(*res), mul

                elif cls.of_simple_poly():
                    i = 1 - cls.args.index(Expr)
                    index = indices[i]
                    [*args] = self.args
                    del args[index]
                    
                    coeff = res[index]
                    if isinstance(coeff, tuple):
                        coeff = Mul(*coeff)
                    return coeff, Add(*args)

            elif len(res) == 2:
                for index, r in enumerate(res):
                    if isinstance(r, tuple):
                        break
                else:
                    return res

                if cls.of_simple_poly() and cls.args.index(Expr) == 1 - index:
                    mul_args = cls.args[index].args
                    coeff = mul_args[1 - mul_args.index(Expr)]
                    if not isinstance(coeff, type) and not isinstance(coeff, Basic):
                        res = [*res]
                        res[index] = Mul(*res[index])
                        res = tuple(res)

        return res

    def of_simple_poly(self, x):
        '''
        extract the coefficients of a simple polynomial
        (a * x + b).of_simple_poly(x) = [b, a]
        '''
        B = None
        A = None
        
        for arg in self.args:
            b, a = arg.of_simple_poly(x)
            if b is None:
                return None, None
            if B is None:
                B = b
                A = a
            else:
                B += b
                A += a
            
        return B, A

    def monotonicity(self, x):
        '''
        determine the Monotonicity of a function wrt to x
        (-l + Min(l, n - Min(n, u))).monotonicity(x) = -1
        (x ** 2).monotonicity(x) = 0
        (a * x + b).monotonicity(x) = 1 if a > 0
        (a * x + b).monotonicity(x) = -1 if a < 0
        '''
        
        monotonic_increasing = []
        monotonic_decreasing = []
        from sympy.functions.elementary.miscellaneous import Max, Min
        coeff = []
        for i, fx in enumerate(self.args):
            if fx._has(x):
                expr, monotonicity = fx.monotonicity(x)
                if monotonicity > 0:
                    monotonic_increasing.append(expr)
                elif monotonicity < 0:
                    monotonic_decreasing.append(expr)
                else:
                    if fx.is_Min and fx._has(Max) or fx.is_Max and fx._has(Min):
# deal with special case :
# k + Min(k, Max(-k, -i + j))
                        const = Add(*self.args[:i] + self.args[i + 1:], evaluate=False)
                        return fx.func(*(arg + const for arg in fx.args), evaluate=False).monotonicity(x)
                        
                    if isinstance(expr, tuple):
                        lower, upper = expr
                        [*args] = self.args
                        args[i] = lower
                        lower = Add(*args)
                        expr_lower, mon_lower = lower.monotonicity(x)
                        
                        args[i] = upper
                        upper = Add(*args)
                        expr_upper, mon_upper = upper.monotonicity(x)

                        if mon_lower < 0:
                            if mon_upper > 0:
                                ...
                            elif mon_upper < 0:
                                ...
                            else:
                                if not upper._has(x):
                                    return (expr_lower, upper), 0
                        elif mon_lower > 0:
                            ...
                        else:
                            if mon_upper > 0:
                                if not lower._has(x):
                                    return (lower, expr_upper), 0
                            elif mon_upper < 0:
                                ...
                            else:
                                if not lower._has(x):
                                    if not upper._has(x):
                                        return (lower, upper), 0
                    return None, 0
            else:
                coeff.append(fx)
        
        i = 0
        j = 0
        while i < len(monotonic_increasing) and j < len(monotonic_decreasing):
            fx = monotonic_increasing[i]
            hx = monotonic_decreasing[j]
            if fx.is_MinMaxBase:
                if ret := fx.merge_monotonicity_with(hx, x):
                    monotonic_decreasing[j] = ret
                    del monotonic_increasing[i]
                    i = 0
                    continue
                
                if hx.is_MinMaxBase:
                    if ret := hx.merge_monotonicity_with(fx, x):
                        monotonic_increasing[i] = ret
                        del monotonic_decreasing[j]
                        j = 0
                        continue

                    j += 1
                else:
                    i += 1
            
            elif hx.is_MinMaxBase:
                if ret := hx.merge_monotonicity_with(fx, x):
                    monotonic_increasing[i] = ret
                    del monotonic_decreasing[j]
                    j = 0
                    continue
                
                j += 1
            else:
                hx_neg = -hx
                if hx_neg.is_MinMaxBase:
                    if ret := hx_neg.merge_monotonicity_with(-fx, x):
                        monotonic_increasing[i] = -ret
                        del monotonic_decreasing[j]
                        j = 0
                    else:
                        j += 1
                        
                    continue
                
                fx_neg = -fx
                if fx_neg.is_MinMaxBase:
                    if ret := fx_neg.merge_monotonicity_with(-hx, x):
                        monotonic_decreasing[j] = -ret
                        del monotonic_increasing[i]
                        i = 0
                    else:
                        i += 1
                        
                    continue
                
                i += 1
                
        if not monotonic_decreasing:
            return Add(*coeff, *monotonic_increasing, evaluate=False), 1
        
        if not monotonic_increasing:
            return Add(*coeff, *monotonic_decreasing, evaluate=False), -1
        
        return None, 0

    __invert__ = _eval_conjugate
    
    def __call__(self, other):
        return self * other

    def is_continuous_at(self, *args):
        from sympy.core.logic import fuzzy_and
        return fuzzy_and(x.is_continuous_at(*args) for x in self.args)

    def as_coeff_Mul(self, rational=False):
        if all(arg._coeff_isneg() for arg in self.args):
            return S.NegativeOne, self.func(*[-arg for arg in self.args], evaluate=False)
            
        return S.One, self
        
    @staticmethod
    def simplify_Lamda(self, squeeze=False):
        vars = self.variables
        limits = self.limits
        modified = []
        unmodified = []
        constants = []
        for arg in self.expr.args:
            if arg.has(*vars):
                if arg.is_Mul:
                    unmodified.append(arg)
                else:
                    lamda = self.func(arg, *limits)
                    _lamda = lamda.simplify()
                    if _lamda != lamda:
                        modified.append(_lamda)
                    else:
                        unmodified.append(arg)
            else:
                constants.append(arg)
    
        if modified or constants:
            if unmodified:
                if max(len(expr.shape) for expr in unmodified) < len(self.expr.shape):
                    return self
                
                if len(unmodified) == 1:
                    unmodified, = unmodified
                    if unmodified.is_Mul:
                        lamda = self.func(unmodified, *limits)
                        _lamda = lamda.simplify()
                        if _lamda != lamda:
                            modified.append(_lamda)
                            unmodified = S.Zero
                            
                    if unmodified:
                        unmodified = self.func(unmodified, *limits)
                else:
                    unmodified = self.func(Add(*unmodified), *limits)
            else:
                unmodified = S.Zero

            return Add(*modified, *constants, unmodified)
        return self

    @property
    def is_comparable(self):
        return all(arg.is_comparable for arg in self.args)

    def rewrite(self, *args, **hints):
        if hints.get('collect'):
            factor = hints.get('factor')
            deep = hints.get('deep')
            common_terms = None
            others = []

            additives = []
            if factor is None:
                muls = []
                for arg in self.args:
                    if arg.is_Mul:
                        if common_terms is None:
                            common_terms = {*arg.args}
                        else:
                            if common_terms & {*arg.args}:
                                common_terms &= {*arg.args}
                            else:
                                others.append(arg)
                                continue
                        muls.append(arg)
                    else:
                        others.append(arg)

                if len(muls) == 1:
                    for i in reversed(range(len(others))):
                        o = others[i]
                        if not o.is_Number and o in common_terms:
                            common_terms = {o}
                            del others[i]
                            additives.append(S.One)
                            break
                    else:
                        muls = []

                for arg in muls:
                    if args := {*arg.args} - common_terms:
                        arg = Mul(*args)
                        additives.append(arg)
                    else:
                        return self
                    
                if len(additives) > 1:
                    factor = Mul(*common_terms)
                    additives = Add(*additives)
                    if additives.is_Add and deep:
                        additives = additives.rewrite(collect=True, deep=True)
                elif args := self.search_for_intersection():
                    # try a better algorithm to find common terms:
                    i, j, common_terms = args
                    others = [*self.args]
                    del others[i]
                    del others[j]
                    
                    if args := Mul.factorize([self.args[i], self.args[j]], common_terms):
                        additives, factor = args
                        if factor.is_Number:
                            return self
                        additives = Add(*additives)
                    else:
                        return self
                else:
                    return self

                return additives * factor + Add(*others) 
            else:
                if isinstance(factor, (tuple, list)):
                    ...
                elif factor.is_Mul:
                    factor = factor.args
                else:
                    factor = factor,
                return self._collect(*factor)

        return super().rewrite(*args, **hints)

    # is not compatible with collect
    def _collect(self, *args):
        additives = []
        others = []
        factor, *factors = args
        for arg in self.args:
            quotient = arg.try_div(factor)
            if quotient is None:
                others.append(arg)
            else:
                additives.append(quotient)

        sgm = Add(*additives)
        if factors:
            sgm = sgm._collect(*factors)

        sgm *= factor
        if others:
            sgm += Add(*others)

        return sgm
    
    @classmethod
    def complement(cls, argset, factor):
        for arg in argset:
            if arg == factor:
                argset.remove(arg)
                return argset

            if arg.is_Pow:
                b, e = arg.args
                if b == factor:
                    if e.is_Integer and e > 1:
                        argset.remove(arg)
                        argset.add(b ** (e - 1))
                        return argset

                    elif e.is_Add:
                        if any(e.is_Integer and e >= 1 for e in e.args):
                            argset.remove(arg)
                            argset.add(b ** (e - 1))
                            return argset

                elif factor.is_Pow and factor.base == b:
                    exp = factor.exp
                    if e.is_Integer:
                        if e > 0 and exp > 0 and e > exp or e < 0 and exp < 0 and e < exp:
                            argset.remove(arg)
                            argset.add(b ** (e - exp))
                            return argset

            elif arg == -factor:
                argset.remove(arg)
                argset.add(S(-1))
                return argset

    def _eval_try_div(self, factor):
        if factor.is_Add:
            if len(self.args) == len(factor.args):
                # precondition: self.is_Add and factor.is_Add
                quotient = set()
                for a, b in zip(self.args, factor.args):
                    q = a.try_div(b)
                    if q is None:
                        break

                    quotient.add(q)
                    if len(quotient) > 1:
                        break
                else:
                    return quotient.pop()
                return
        else:
            args = []
            for i, arg in enumerate(self.args):
                quotient = arg.try_div(factor)
                if quotient is None:
                    return
                args.append(quotient)
            return Add(*args)

    @classmethod
    def intersect_args(cls, lhs, rhs):
        ret = set()
        for x in lhs:
            for y in rhs:
                if x == y:
                    # if not x.is_Number:
                    ret.add(x)
                    break

                elif y.is_Pow:
                    if z := y.extract_pow(x):
                        ret.add(z)
                        break

                elif x == -y:
                    if x.is_Mul:
                        if x._coeff_isneg():
                            ret.add(y)
                        else:
                            ret.add(y)

                    elif x.is_Add and y.is_Add:
                        if x.args[0]._coeff_isneg() and y.args[0]._coeff_isneg():
                            ret.add(y)
                        else:
                            ret.add(x)
                    else:
                        ret.add(x)
                    break

                elif x.is_Pow:
                    if z := x.extract_pow(y):
                        ret.add(z)
                        break

        return ret

    def search_for_intersection(self):
        args = self.args
        for i in range(1, len(args)):
            for j in range(i):
                # j < i
                if ret := Add.intersect_args(args[i].args if args[i].is_Mul else [args[i]], args[j].args if args[j].is_Mul else [args[j]]):
                    return i, j, ret

from .mul import Mul, _keep_coeff, prod
from sympy.core.numbers import Rational
