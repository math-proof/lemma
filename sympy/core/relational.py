from .add import Add
from .basic import S, Atom
from .compatibility import ordered
from .basic import Basic
from .evalf import EvalfMixin
from .function import AppliedUndef
from .sympify import _sympify
from .parameters import global_parameters
from sympy.core.logic import fuzzy_bool, fuzzy_xor, fuzzy_and, fuzzy_not
from sympy.logic.boolalg import Boolean, BooleanAtom, BinaryCondition
from sympy.core.sympify import sympify, SympifyError
from sympy.core.cache import cacheit

from .expr import Expr
from sympy.multipledispatch import dispatch
from .containers import Tuple
from .symbol import Symbol


# Note, see issue 4986.  Ideally, we wouldn't want to subclass both Boolean
# and Expr.
# from .. import Expr


def _canonical(cond):
    # return a condition in which all relationals are canonical
    reps = {r: r.canonical for r in cond.atoms(Relational)}
    return cond.xreplace(reps)
    # XXX: AttributeError was being caught here but it wasn't triggered by any of
    # the tests so I've removed it...


# from sympy.logic.boolalg import Boolean
class Relational(BinaryCondition, Expr, EvalfMixin):
    """Base class for all relation types.

    Explanation
    ===========

    Subclasses of Relational should generally be instantiated directly, but
    Relational can be instantiated with a valid ``rop`` value to dispatch to
    the appropriate subclass.

    Parameters
    ==========

    rop : str or None
        Indicates what subclass to instantiate.  Valid values can be found
        in the keys of Relational.ValidRelationOperator.

    Examples
    ========

    >>> from sympy import Rel
    >>> from sympy.abc import x, y
    >>> Rel(y, x + x**2, '==')
    Eq(y, x**2 + x)

    """
    __slots__ = ()

    ValidRelationOperator = {}  # type: Dict[Union[str, None], Type[Relational]]

    _op_priority = 12  # higher than Expr
    # ValidRelationOperator - Defined below, because the necessary classes
    #   have not yet been defined

    def __new__(cls, lhs, rhs, rop=None, **assumptions):

        # If called by a subclass, do nothing special and pass on to Expr.

        if cls is not Relational:
            return BinaryCondition.__new__(cls, lhs, rhs, **assumptions)
        # If called directly with an operator, look up the subclass
        # corresponding to that operator and delegate to it
        try:
            cls = cls.ValidRelationOperator[rop]
            rv = cls(lhs, rhs, **assumptions)
            # /// drop when Py2 is no longer supported
            # validate that Booleans are not being used in a relational
            # other than Eq/Ne;
            if isinstance(rv, (Eq, Ne)):
                pass
            elif isinstance(rv, Relational):  # could it be otherwise?
                from sympy.core.symbol import Symbol

                for a in rv.args:
                    if isinstance(a, Symbol):
                        continue
                    if isinstance(a, Boolean):
                        from sympy.utilities.misc import filldedent
                        raise TypeError(filldedent('''
                            A Boolean argument can only be used in
                            Eq and Ne; all other relationals expect
                            real expressions.
                        '''))
            # \\\
            return rv
        except KeyError:
            raise ValueError(
                "Invalid relational operator symbol: %r" % rop)

    @property
    def lhs(self):
        """The left-hand side of the relation."""
        return self._args[0]

    @property
    def rhs(self):
        """The right-hand side of the relation."""
        return self._args[1]

    @property
    def reversed(self):
        """Return the relationship with sides reversed.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> Eq(x, 1)
        Eq(x, 1)
        >>> _.reversed
        Eq(1, x)
        >>> x < 1
        x < 1
        >>> _.reversed
        1 > x
        """
        a, b = self.args
        return self.reversed_type(b, a, sympify=False, evaluate=False)

    def __neg__(self, **kwargs):
        """Return the relationship with signs reversed.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> Eq(x, 1)
        Eq(x, 1)
        >>> -_
        Eq(-x, -1)
        >>> x < 1
        x < 1
        >>> -_
        -x > -1
        """

        lhs, rhs = -self.lhs, -self.rhs
        lhs, rhs = lhs.simplify(), rhs.simplify()
        return self.reversed_type(lhs, rhs)

    def _eval_evalf(self, prec):
        return self.func(*[s._evalf(prec) for s in self.args])

    @property
    def canonical(self):
        """Return a canonical form of the relational by putting a
        number on the rhs, canonically removing a sign or else
        ordering the args canonically. No other simplification is
        attempted.

        Examples
        ========

        >>> from sympy.abc import x, y
        >>> x < 2
        x < 2
        >>> _.reversed.canonical
        x < 2
        >>> (-y < x).canonical
        x > -y
        >>> (-y > x).canonical
        x < -y
        >>> (-y < -x).canonical
        x < y
        """
        args = self.args
        r = self
        if r.rhs.is_number:
            if r.rhs.is_Number and r.lhs.is_Number and r.lhs > r.rhs:
                r = r.reversed
        elif r.lhs.is_number:
            r = r.reversed
        elif tuple(ordered(args)) != args:
            r = r.reversed

        # Check if first value has negative sign
        if not isinstance(r.lhs, BooleanAtom) and \
                r.lhs.could_extract_minus_sign():
            r = -r
        elif not isinstance(r.rhs, BooleanAtom) and not r.rhs.is_number and \
                r.rhs.could_extract_minus_sign():
            # Right hand side has a minus, but not lhs.
            # How does the expression with reversed signs behave?
            # This is so that expressions of the type Eq(x, -y) and Eq(-x, y)
            # have the same canonical representation
            expr1, _ = ordered([r.lhs, -r.rhs])
            if expr1 != r.lhs:
                r = -r.reversed
        return r

    def equals(self, other, failing_expression=False):
        """Return True if the sides of the relationship are mathematically
        identical and the type of relationship is the same.
        If failing_expression is True, return the expression whose truth value
        was unknown."""
        if isinstance(other, Relational):
            if self == other or self.reversed == other:
                return True
            a, b = self, other
            if a.func in (Eq, Ne) or b.func in (Eq, Ne):
                if a.func != b.func:
                    return False
                left, right = [i.equals(j,
                                        failing_expression=failing_expression)
                               for i, j in zip(a.args, b.args)]
                if left is True:
                    return right
                if right is True:
                    return left
                lr, rl = [i.equals(j, failing_expression=failing_expression)
                          for i, j in zip(a.args, b.reversed.args)]
                if lr is True:
                    return rl
                if rl is True:
                    return lr
                e = (left, right, lr, rl)
                if all(i is False for i in e):
                    return False
                for i in e:
                    if i not in (True, False):
                        return i
            else:
                if b.func != a.func:
                    b = b.reversed
                if a.func != b.func:
                    return False
                left = a.lhs.equals(b.lhs,
                                    failing_expression=failing_expression)
                if left is False:
                    return False
                right = a.rhs.equals(b.rhs,
                                     failing_expression=failing_expression)
                if right is False:
                    return False
                if left is True:
                    return right
                return left

    def _eval_simplify(self, ratio, measure, rational, inverse):
        from sympy.simplify import simplify
        r = self
        r = r.func(*[simplify(i, ratio=ratio, measure=measure, rational=rational, inverse=inverse) for i in r.args])
        if r.is_Relational:
            diff = r.lhs - r.rhs
            # replace diff with a valid Number that will
            # allow a definitive comparison with 0
            v = None
            if diff.is_comparable:
                v = diff.n(2)
            elif diff.equals(0):  # XXX this is expensive
                v = S.Zero
            if v is not None:
                r = r.func._eval_relation(v, S.Zero)

        r = r.canonical
        if measure(r) < ratio * measure(self):
            return r
        else:
            return self

    def _eval_trigsimp(self, **opts):
        from sympy.simplify import trigsimp
        return self.func(trigsimp(self.lhs, **opts), trigsimp(self.rhs, **opts))

    def expand(self, *args, **kwargs):
        return self.func(self.lhs.expand(*args, **kwargs), self.rhs.expand(*args, **kwargs))

    def _eval_as_set(self):
        # self is univariate and periodicity(self, x) in (0, None)
        from sympy.solvers.inequalities import solve_univariate_inequality
        syms = self.free_symbols
        assert len(syms) == 1
        x, = syms
        return solve_univariate_inequality(self, x, relational=False)

    @property
    def binary_symbols(self):
        # override where necessary
        return set()

    def simplify(self, deep=False, wrt=None, **kwargs):
        if deep or wrt is not None:
            return BinaryCondition.simplify(self, deep=True, wrt=wrt)        

        lhs, rhs = self.args
        this = self.lhs.func.simplify_Relational(self, lhs, rhs)
        if this is not None:
            return this
        
        if rhs.is_Mul:
            if rhs.args[0].is_Ones:
                if lhs.shape == rhs.shape:
                    rhs = rhs.func(*rhs.args[1:])
                    return self.func(lhs, rhs, evaluate=False)
        elif rhs.is_Ones:
            if lhs.shape == rhs.shape:
                return self.func(lhs, S.One, evaluate=False)
                
        return self

    def doit(self, *args, **kwargs):
        return self.func(self.lhs.doit(*args, **kwargs), self.rhs.doit(*args, **kwargs))

    def __add__(self, other, **kwargs):
        other = sympify(other)
        if isinstance(other, Equal):
            return self.func(self.lhs + other.lhs, self.rhs + other.rhs, **other.add_sub_assumptions(self)).simplify()
        elif isinstance(other, Relational):
            return other.func(self.lhs + other.lhs, self.rhs + other.rhs, given=[self, other]).simplify()
        elif other.is_Quantifier:
            return self.bfn(self.__add__, other)
        else:
            assert other.is_complex, 'try to prove %s is complex' % other
            return self.func(self.lhs + other, self.rhs + other)

    def __sub__(self, other, **kwargs):
        other = sympify(other)
        if other.is_Equal: 
            return self.func(self.lhs - other.lhs, self.rhs - other.rhs, **other.add_sub_assumptions(self))
        elif other.is_Quantifier:
            return self.bfn(self.__sub__, other)
        else: 
            assert not other.is_set
            assert other.is_complex, 'try to prove %s is complex' % other
            return self.func((self.lhs - other).simplify(), (self.rhs - other).simplify())

    def __mul__(self, other, **kwargs):
        if isinstance(other, Equal):
            if other.lhs.is_nonzero or other.rhs.is_nonzero:
                return self.func(self.lhs * other.lhs, self.rhs * other.rhs)
            return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        else:
            other = sympify(other)
            if other.is_extended_positive:
                return self.func(self.lhs * other, self.rhs * other)
            if other.is_extended_negative:
                return self.reversed_type(self.lhs * other, self.rhs * other)
            elif other.is_extended_nonnegative:
                return self.func(self.lhs * other, self.rhs * other, given=self)
            elif other.is_extended_nonpositive:
                return self.reversed_type(self.lhs * other, self.rhs * other, given=self)
            return self

    def __truediv__(self, other, **kwargs):
        if isinstance(other, Equal):
            if other.lhs.is_nonzero or other.rhs.is_nonzero:
                return self.func(self.lhs / other.lhs, self.rhs / other.rhs)
            return self
        else:
            other = sympify(other)
            if other.is_extended_positive:
                return self.func((self.lhs / other).ratsimp(), (self.rhs / other).ratsimp())
            if other.is_extended_negative:
                return self.reversed_type((self.lhs / other).ratsimp(), (self.rhs / other).ratsimp())
            return self

    def __iter__(self):
        raise TypeError

    def solve(self, x):
        from sympy.sets.contains import Element
        if not x.is_Symbol:
            _x = self.generate_var(x.free_symbols, **x.type.dict)
            this = self._subs(x, _x)
            domain = _x.domain_conditioned(this)            
            domain = domain._subs(_x, x)
        else:
            domain = x.domain_conditioned(self)
            
        if domain.is_ConditionSet:
            self
            
        return Element(x, domain).simplify()

    def is_positive_relationship(self):
        ...

    def _sympystr(self, p):
        from sympy.printing.precedence import precedence
        charmap = {
            "==": "Eq",
            "!=": "Ne",
            ":=": "Assignment",
            '+=': "AddAugmentedAssignment",
            "-=": "SubAugmentedAssignment",
            "*=": "MulAugmentedAssignment",
            "/=": "DivAugmentedAssignment",
            "%=": "ModAugmentedAssignment",
        }

        if self.rel_op in charmap:
            return '%s(%s, %s)' % (charmap[self.rel_op], p._print(self.lhs),
                                   p._print(self.rhs))

        return '%s %s %s' % (p.parenthesize(self.lhs, precedence(self)),
                           p._relationals.get(self.rel_op) or self.rel_op,
                           p.parenthesize(self.rhs, precedence(self)))

    def _lean(self, p):
        from sympy.printing.precedence import precedence
        charmap = {
            "==": "Eq",
            "!=": "Ne",
            ":=": "Assignment",
            '+=': "AddAugmentedAssignment",
            "-=": "SubAugmentedAssignment",
            "*=": "MulAugmentedAssignment",
            "/=": "DivAugmentedAssignment",
            "%=": "ModAugmentedAssignment",
        }

        if self.rel_op in charmap:
            return '%s(%s, %s)' % (charmap[self.rel_op], p._print(self.lhs),
                                   p._print(self.rhs))

        return '%s %s %s' % (p.parenthesize(self.lhs, precedence(self)),
                           p._relationals.get(self.rel_op) or self.rel_op,
                           p.parenthesize(self.rhs, precedence(self)))

    def _latex(self, p):
        if p._settings['itex']:
            gt = r"\gt"
            lt = r"\lt"
        else:
            gt = ">"
            lt = "<"

        charmap = {
            "==": "=",
            ">": gt,
            "<": lt,
            ">=": r"\geq",
            "<=": r"\leq",
            "!=": r"\neq",
        }

        return "%s %s %s" % (p._print(self.lhs), charmap[self.rel_op], p._print(self.rhs))

    def domain_conditioned_utility(self, var):
        if self.lhs.is_set or var.shape or var.is_set:
            return
        
        equation = self.lhs - self.rhs
        p = equation.as_poly(var)
        if not p or p.degree() != 1:
            return
         
        a = p.nth(1)
        if a.is_nonzero:
            b = p.nth(0)
            solution = -b / a
            return a, solution, var.domain & self.domain_defined(var)

    @cacheit
    def _eval_domain_defined(self, x, **_):
        return self.lhs.domain_defined(x, real=x.is_real) & self.rhs.domain_defined(x, real=x.is_real)

    def invert(self):
        lhs, rhs = self.args
        
        if len(lhs.shape) < len(rhs.shape):
            shape = rhs.shape
        else:
            shape = lhs.shape

        if shape:
            excludes = set()
            indices = []
            limits = []
            for n in shape:
                i = self.generate_var(excludes, integer=True)
                excludes.add(i)
                indices.append(i)
                limits.append((i, 0, n))
                
            indices = tuple(indices)
            
            if len(lhs.shape) < len(rhs.shape):
                lhs_indices = indices[len(rhs.shape) - len(lhs.shape):]
                if lhs_indices:
                    lhs = lhs[lhs_indices]
                rhs = rhs[indices]                
            elif len(lhs.shape) > len(rhs.shape):
                rhs_indices = indices[len(lhs.shape) - len(rhs.shape):]
                if rhs_indices:
                    rhs = rhs[rhs_indices]
                lhs = lhs[indices]
            else:
                lhs, rhs = lhs[indices], rhs[indices]
            
            eq = Boolean.__new__(self.invert_type, lhs, rhs)
            from sympy.concrete.exists import Any
            return Any(eq, *limits[::-1])
        
        return BinaryCondition.invert(self)

    @classmethod
    def class_key(cls):
        """Nice order of classes. """
        return 5, cls.sub_class_key(), cls.__name__


Rel = Relational


class Equal(Relational):
    """An equal relation between two objects.

    Explanation
    ===========

    Represents that two objects are equal.  If they can be easily shown
    to be definitively equal (or unequal), this will reduce to True (or
    False).  Otherwise, the relation is maintained as an unevaluated
    Equal object.  Use the ``simplify`` function on this object for
    more nontrivial evaluation of the equality relation.

    As usual, the keyword argument ``evaluate=False`` can be used to
    prevent any evaluation.

    Examples
    ========

    >>> from sympy import Eq, simplify, exp, cos
    >>> from sympy.abc import x, y
    >>> Eq(y, x + x**2)
    Eq(y, x**2 + x)
    >>> Eq(2, 5)
    False
    >>> Eq(2, 5, evaluate=False)
    Eq(2, 5)
    >>> _.doit()
    False
    >>> Eq(exp(x), exp(x).rewrite(cos))
    Eq(exp(x), sinh(x) + cosh(x))
    >>> simplify(_)
    True

    See Also
    ========

    sympy.logic.boolalg.Equivalent : for representing equality between two
        boolean expressions

    Notes
    =====

    Python treats 1 and True (and 0 and False) as being equal; SymPy
    does not. And integer will always compare as unequal to a Boolean:

    >>> Eq(True, 1), True == 1
    (False, True)

    This class is not the same as the == operator.  The == operator tests
    for exact structural equality between two expressions; this class
    compares expressions mathematically.

    If either object defines an `_eval_Eq` method, it can be used in place of
    the default algorithm.  If `lhs._eval_Eq(rhs)` or `rhs._eval_Eq(lhs)`
    returns anything other than None, that return value will be substituted for
    the Equal.  If None is returned by `_eval_Eq`, an Equal object will
    be created as usual.

    Since this object is already an expression, it does not respond to
    the method `as_expr` if one tries to create `x - y` from Eq(x, y).
    This can be done with the `rewrite(Add)` method.
    """
    rel_op = '=='

    __slots__ = ()

    def __new__(cls, lhs, rhs=None, **options):
        if options.pop('sympify', True):
            lhs = _sympify(lhs)
            rhs = _sympify(rhs)
        if options.pop('evaluate', global_parameters.evaluate):
            # If one expression has an _eval_Eq, return its results.
            if hasattr(lhs, '_eval_Eq'):
                r = lhs._eval_Eq(rhs)
                if isinstance(r, BooleanAtom):
                    return r.copy(**options)
            if hasattr(rhs, '_eval_Eq'):
                r = rhs._eval_Eq(lhs)
                if isinstance(r, BooleanAtom):
                    return r.copy(**options)
            # If expressions have the same structure, they must be equal.
            if lhs == rhs or lhs.dummy_eq(rhs):
                return S.true.copy(**options)  # e.g. True == True
            elif all(isinstance(i, BooleanAtom) for i in (rhs, lhs)):
                return S.false  # True != False
            elif not (lhs.is_Symbol or rhs.is_Symbol) and (lhs.is_Boolean != rhs.is_Boolean):
                return S.false  # only Booleans can equal Booleans
            from sympy.sets.contains import Element
            if Element(rhs, lhs.domain, sympify=False).is_BooleanFalse or Element(lhs, rhs.domain, sympify=False).is_BooleanFalse:
                return S.false.copy(**options)

            if isinstance(lhs, Expr) and isinstance(rhs, Expr) and not lhs.dtype.is_set and not rhs.dtype.is_set and not lhs.dtype.is_bool:
                # see if the difference evaluates
                if lhs.is_infinite:
                    if rhs.is_infinite:
                        if lhs == rhs:
                            return S.true.copy(**options)
                        else:
                            return S.false.copy(**options)
                    else:  
                        ...
                else:
                    if rhs.is_infinite:
                        ...
                    else:                       
                        diff = (lhs - rhs).simplify()
                        z = diff.is_zero
                        if z is not None:
                            if z is False:
                                return S.false.copy(**options)
                            if z:
                                if 'plausible' in options:
                                    del options['plausible']
                                else:
                                    return S.true.copy(**options)
        if options:
            from sympy.core.inference import Inference
            return Inference(Relational.__new__(cls, lhs, rhs), **options)

        return Relational.__new__(cls, lhs, rhs, **options)

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        return _sympify(lhs == rhs)

    def _eval_rewrite_as_Add(self, *args, **kwargs):
        """
        return Eq(L, R) as L - R. To control the evaluation of
        the result set pass `evaluate=True` to give L - R;
        if `evaluate=None` then terms in L and R will not cancel
        but they will be listed in canonical order; otherwise
        non-canonical args will be returned.

        Examples
        ========

        >>> from sympy import Eq, Add
        >>> from sympy.abc import b, x
        >>> eq = Eq(x + b, x - b)
        >>> eq.rewrite(Add)
        2*b
        >>> eq.rewrite(Add, evaluate=None).args
        (b, b, x, -x)
        >>> eq.rewrite(Add, evaluate=False).args
        (b, x, b, -x)
        """
        from .add import _unevaluated_Add, Add
        L, R = args
        evaluate = kwargs.get('evaluate', True)
        if evaluate:
            # allow cancellation of args
            return L - R
        args = Add.make_args(L) + Add.make_args(-R)
        if evaluate is None:
            # no cancellation, but canonical
            return _unevaluated_Add(*args)
        # no cancellation, not canonical
        return Add._from_args(args)

    @property
    def binary_symbols(self):
        if S.true in self.args or S.false in self.args:
            if self.lhs.is_Symbol:
                return {self.lhs}
            elif self.rhs.is_Symbol:
                return {self.rhs}
        return set()

    def _eval_simplify(self, **kwargs):
        from sympy.solvers.solveset import linear_coeffs
        # standard simplify
        e = super()._eval_simplify(**kwargs)
        if not isinstance(e, Equal):
            return e
        free = self.free_symbols
        if len(free) == 1:
            try:
                x, = free
                m, b = linear_coeffs(
                    e.rewrite(Add, evaluate=False), x)
                if m.is_zero == False:
                    enew = e.func(x, -b / m)
                else:
                    enew = e.func(m * x, -b)
                measure = kwargs['measure']
                if measure(enew) <= kwargs['ratio'] * measure(e):
                    e = enew
            except ValueError:
                pass
        return e.canonical

    def __truediv__(self, other, **kwargs):
        other = sympify(other)
        if other.is_Equal:
            if other.lhs.is_nonzero or other.rhs.is_nonzero:
                return self.func((self.lhs / other.lhs).ratsimp(), (self.rhs / other.rhs).ratsimp())
            return self
        else:
            lhs = (self.lhs / other).ratsimp().simplify()
            rhs = (self.rhs / other).ratsimp().simplify()
            if other.is_nonzero:
                return self.func(lhs, rhs)
            from sympy import Or
            return Or(self.func(other, 0), self.func(lhs, rhs))

    def __rmul__(self, lhs, **kwargs):
        return self.__mul__(lhs, **kwargs)
        
    def __mod__(self, other, **kwargs):
        other = sympify(other)
        assert other.is_integer
        return Eq(self.lhs % other, self.rhs % other, given=self)
     
    def __mul__(self, other, **kwargs):
        other = sympify(other)
        if isinstance(other, Equal):
            if other.lhs.is_nonzero or other.rhs.is_nonzero:
                return Eq(self.lhs * other.lhs, self.rhs * other.rhs)
            return Eq(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])

        elif isinstance(other, Less):
            if other.lhs.is_extended_positive:
                return Less(self.lhs * other.lhs, self.rhs * other.rhs)
            elif other.lhs.is_extended_nonnegative:
                if other.lhs.is_nonzero or other.rhs.is_nonzero:
                    return Eq(self.lhs * other.lhs, self.rhs * other.rhs)
                return Eq(self.lhs * other.lhs, self.rhs * other.rhs, given=self)

            elif other.rhs.is_extended_negative:
                if other.lhs.is_nonzero or other.rhs.is_nonzero:
                    return Eq(self.lhs * other.lhs, self.rhs * other.rhs)
                return Eq(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])

            elif other.rhs.is_extended_nonpositive:
                if other.lhs.is_nonzero or other.rhs.is_nonzero:
                    return Eq(self.lhs * other.lhs, self.rhs * other.rhs)
                return Eq(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])

            return self
        else:
            if other.is_nonzero:
                return Eq(self.lhs * other, self.rhs * other)
            return Eq(self.lhs * other, self.rhs * other, given=self)

    def __rmatmul__(self, lhs, **kwargs):
        if isinstance(lhs, Equal):
            if lhs.lhs.is_invertible or lhs.rhs.is_invertible:
                return Eq(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs)
            return Eq(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs, given=[self, lhs])
        else:
            if lhs.is_invertible:
                return Eq(lhs @ self.lhs, lhs @ self.rhs, equivalent=self)
            return Eq(lhs @ self.lhs, lhs @ self.rhs, given=self)

    def __matmul__(self, rhs, **kwargs):
        if isinstance(rhs, Equal):
            if rhs.lhs.is_invertible or rhs.rhs.is_invertible:
                return self.func(self.lhs @ rhs.lhs, self.rhs @ rhs.rhs)
            return self.func(self.lhs @ rhs.lhs, self.rhs @ rhs.rhs, given=[self, rhs])

        else: 
            if rhs.is_invertible:
                return self.func(self.lhs @ rhs, self.rhs @ rhs, equivalent=self)
            return self.func(self.lhs @ rhs, self.rhs @ rhs, given=self)

    def __rpow__(self, other, **kwargs):
        if other.is_positive:
            return self.func(other ** self.lhs, other ** self.rhs)
        
        if self.lhs.is_positive or self.rhs.is_positive:
            return self.func(other ** self.lhs, other ** self.rhs, given=self)
        
        return self

    def __pow__(self, other, **kwargs):
        other = sympify(other)
        if other.is_positive:
            return self.func(self.lhs ** other, self.rhs ** other, given=self)
        return self
        
    def powsimp(self, *args, **kwargs):
        return Eq(self.lhs.powsimp(*args, **kwargs), self.rhs.powsimp(*args, **kwargs))

    def collect(self, syms):
        return Eq(self.lhs.collect(syms), self.rhs.collect(syms))

    def rsolve(self, y):
        from sympy.solvers.recurr import rsolve
        solution = rsolve(self, y, symbols=True)
        if solution is None:
            return self
        solution, limits = solution
        
        eq = self.func(y, solution)
        if len(limits) == 0:
            eq.equivalent = self
            return eq
        from sympy import Any
        for i, C in enumerate(limits):
            limits[i] = (C,)
        return Any(eq, *limits)

    def solve(self, x):
        from sympy.solvers.solvers import solve
        res = solve(self.lhs - self.rhs, x)

        if len(res) == 1:
            x_sol, *_ = res
            return Eq(x, x_sol)
        if len(res) > 1:
            from sympy.logic.boolalg import Or
            return Or(*(self.func(x, x_sol) for x_sol in res))

        return self

    def subs(self, *args, simplify=True, **kwargs):
        [*args] = map(sympify, args)
        if len(args) == 1:
            arg = args[0]
            if isinstance(arg, dict):
                if 'simultaneous' in kwargs:
                    if self.plausible:
                        return self
                    return self.func(self.lhs.subs(*args, **kwargs).simplify(), self.rhs.subs(*args, **kwargs).simplify()).simplify()
                else:
                    subs = self
                    for key, value in arg.items():
                        subs = subs.subs(key, value)
                    return subs
            elif isinstance(arg, Equal):
                eq = arg
                args = eq.args
                
                lhs = self.lhs._subs(*args, simplify=simplify, **kwargs)
                rhs = self.rhs._subs(*args, simplify=simplify, **kwargs)
                
                if simplify:
                    lhs = lhs.simplify()
                    rhs = rhs.simplify()
                if lhs == self.lhs and rhs == self.rhs:
                    return self
                
                result = self.func(lhs, rhs)
                return self.subs_assumptions_for_equality(eq, result, simplify=simplify)
            elif arg.is_Quantifier:
                return self.bfn(self.subs, arg)
            else:
                return self

        if all(isinstance(arg, Boolean) for arg in args):
            res = self
            for eq in args:
                res = res.subs(eq)
            return res

        return BinaryCondition.subs(self, *args, **kwargs)

    def __getitem__(self, indices, **kwargs):
        from sympy import All
        if isinstance(indices, slice):
            x, *args = indices.start, indices.stop, indices.step
            if x is None or not x.is_symbol or args[1] is None and args[0].is_integer:
                assert indices.step is None
                start, stop = indices.start, indices.stop
                size = self.lhs.shape[0]
                assert self.lhs.shape == self.rhs.shape
                assert start is None or start >= 0, "try to prove %s >= 0" % start
                
                if stop <= size:
                    ...
                elif stop.is_symbol:
                    _stop = stop.definition
                    assert _stop is not None and _stop <= size, "try to prove %s <= %s" % (stop, size)
                else:
                    raise Exception("try to prove %s <= %s" % (stop, size))
                
                return self.func(self.lhs[indices], self.rhs[indices], given=self)
            else:
                if x.is_bounded:
                    x = x.unbounded
                m = self.lhs.shape[0]
                is_equivalent = False
                if len(args) == 2:
                    if args[0] == 0 and args[1] == m:
                        is_equivalent = True
                else:
                    assert len(args) == 1
                    if args[0] == m:
                        is_equivalent = True
                if is_equivalent:
                    return self.func(self.lhs[x], self.rhs[x])
                else:
                    All(self.func(self.lhs[x], self.rhs[x]), (x, *args), given=self)
        return self.func(self.lhs[indices], self.rhs[indices], given=self)

    def combsimp(self, *args):
        from sympy import combsimp
        return self.func(combsimp(self.lhs, *args), combsimp(self.rhs, *args))

    def simplify(self, deep=False, wrt=None, **kwargs):
        if deep or wrt is not None:
            return BinaryCondition.simplify(self, deep=True, wrt=wrt)        

        lhs, rhs = self.args
        this = self.lhs.func.simplify_Equal(self, lhs, rhs)
        if this is not None:
            return this
        
        this = self.rhs.func.simplify_Equal(self, rhs, lhs)
        if this is not None:
            return this
        
        return self

    @classmethod
    def simplify_ForAll(cls, self, function, *limits):
        limits_dict = self.limits_dict
        x = None
        if self.expr.lhs in limits_dict:
            x = self.expr.lhs
            y = self.expr.rhs
        elif self.expr.rhs in limits_dict:
            x = self.expr.rhs
            y = self.expr.lhs

        if x is not None and not y._has(x):
            domain = limits_dict[x]
            if isinstance(domain, Boolean):
                function = domain._subs(x, y)
                if function == False:
                    function = self.limits_cond.invert()
                    return function

    def simplify_Intersection(self, lhs):
        if len(lhs.args) == 2:
            A, B = lhs.args
            if A.is_FiniteSet and B.is_FiniteSet:
                if len(A) == len(B) == 1:
                    return Unequal(A.arg, B.arg)
        
    @property
    def T(self):
        return self.func(self.lhs.T, self.rhs.T)

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_Equal:
            if self.lhs == other.rhs:
                eq = Equal(self.rhs, other.lhs)
                if eq:
                    return self
                if eq == False:
                    return S.false
                
            elif self.lhs == other.lhs:
                eq = Equal(self.rhs, other.rhs)
                if eq:
                    return self
                if eq == False:
                    return S.false
                
        elif isinstance(other, (Less, Greater)):
            if set(self.args) == set(other.args):
                return S.false

        elif other.is_GreaterEqual or other.is_LessEqual:
            if set(self.args) == set(other.args):
                return self
            
        elif other.is_Unequal:
            return other.__and__(self)

        elif other.is_NotElement:
            if self.lhs == other.lhs:
                if self.rhs in other.rhs:
                    return S.false
            elif self.rhs == other.lhs:
                if self.lhs in other.rhs:
                    return S.false
        elif other.is_Element:
            from sympy import Element
            if self.lhs == other.lhs:
                cond = Element(self.rhs, other.rhs) 
                if cond == False:
                    return S.false
                
                if cond:
                    return self
            elif self.rhs == other.lhs:
                cond = Element(self.lhs, other.rhs)
                if cond == False:
                    return S.false

                if cond:
                    return self

        return Relational.__and__(self, other)

    def add_sub_assumptions(self, other):
        kwargs = {}
        if other.lhs.is_set:
            if self.plausible is None:
                if other.plausible is None:
                    kwargs['equivalent'] = self
                else:
                    kwargs['given'] = other
            else:
                kwargs['given'] = [self, other]
        else:
            if other.plausible is None:
                if other.is_Equal or self.plausible is None:
                    kwargs['equivalent'] = self
                else:
                    kwargs['given'] = self
            elif self.plausible is None:
                kwargs['equivalent'] = other
            else:
                kwargs['given'] = [self, other]
        return kwargs
        
    def __add__(self, other, **kwargs):
        if isinstance(other, Relational):
            return other.func(self.lhs + other.lhs, self.rhs + other.rhs, **self.add_sub_assumptions(other)).simplify()
        return Relational.__add__(self, other)
        
    def __rsub__(self, other, **kwargs):
        other = sympify(other)
        assert not isinstance(other, Relational) 
        return self.func(other - self.lhs, other - self.rhs).simplify()
     
    def __sub__(self, other, **kwargs):
        if isinstance(other, Relational): 
            return other.reversed_type((self.lhs - other.lhs).simplify(), (self.rhs - other.rhs).simplify(), **self.add_sub_assumptions(other)).simplify()
        return Relational.__sub__(self, other)

    def __or__(self, other):
        if other.is_Greater:
            if {*other.args} == {*self.args}:
                return GreaterEqual(*other.args)
        elif other.is_Less:
            if {*other.args} == {*self.args}:
                return LessEqual(*other.args)
        elif other.is_LessEqual:
            if {*other.args} == {*self.args}:
                return other
            if self.lhs == other.lhs and self.lhs.is_integer and self.rhs == other.rhs + 1:
#                 x == 3 and x <= 2 => x <= 3
                return LessEqual(*self.args)
        elif other.is_GreaterEqual:
            if {*other.args} == {*self.args}:
                return other
            if self.lhs == other.lhs and self.lhs.is_integer and self.rhs + 1 == other.rhs:
#                 x == 3 and x >= 2 => x >= 3
                return GreaterEqual(*self.args)
            
        return Relational.__or__(self, other)

    def simplify_condition_on_random_variable(self):
        lhs, rhs = self.args
        from sympy.stats.rv import pspace
        if lhs.is_symbol and pspace(lhs).symbol == rhs:
            return lhs
        return self

    def _latex(self, p):
        lhs = self.lhs
        rhs = self.rhs

        if lhs.is_random and lhs.is_symbol:
            if rhs == lhs.var:
                return lhs._latex(p)
            if rhs.is_Surrogate and rhs.arg == lhs:
                return rhs._latex(p)
            
        if lhs.is_Conditioned or rhs.is_Conditioned:
            lex = r"{%s}{\color{blue}{\ =\ }}{%s}"
        else:
            lex = "{%s}={%s}"
        return lex % (p._print(lhs), p._print(rhs))

    def _sympystr(self, p):
        lhs = self.lhs
        rhs = self.rhs

        if lhs.is_random and lhs.is_symbol:
            if rhs == lhs.var:
                return lhs._sympystr(p)
            if rhs.is_Surrogate and rhs.arg == lhs:
                return rhs._sympystr(p)
            
        return "Equal(%s, %s)" % (p._print(lhs), p._print(rhs))

    def _lean(self, p):
        lhs = self.lhs
        rhs = self.rhs

        if lhs.is_random and lhs.is_symbol:
            if rhs == lhs.var:
                return lhs._sympystr(p)
            if rhs.is_Surrogate and rhs.arg == lhs:
                return rhs._sympystr(p)
            
        return "%s = %s" % (p._print(lhs), p._print(rhs))

    def domain_conditioned(self, var):
        lhs, rhs = self.args
        if var.shape:
            if lhs == var:
                return rhs.set
            
            if rhs == var:
                return lhs.set
            
            return BinaryCondition.domain_conditioned(self, var)
        
        if var.is_set:
            if self._has(var):
                from sympy.sets.sets import conditionset
                return conditionset(var, self, var.domain)
            from sympy import Piecewise
            return Piecewise((var.domain, self), (var.emptySet, True))

        if ret := self.domain_conditioned_utility(var):
            a, solution, domain = ret
            return domain & {solution}

        if lhs.is_Mod:
            if lhs.args[0] == var:
                d = lhs.args[1]
                if d > 0 and rhs >= 0 and rhs < d:
                    # x % d == t => x in Range(t, oo, d)
                    from sympy import Range, oo
                    domain = var.domain & self.domain_defined(var)
                    return domain & (Range(rhs, oo, d) | Range(rhs - d, -oo, -d))
                
        return BinaryCondition.domain_conditioned(self, var)

    def of(self, cls):
        res = Boolean.of(self, cls)
        if res is None:
            if cls.is_Equal and len(cls.args) == 2:
                a, b = cls.args
                cls = Basic.__new__(Equal, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number or b.is_EmptySet:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return a, b
        elif isinstance(res, tuple):
            if cls.is_Equal:
                args = cls.args
                if isinstance(args, tuple) and len(args) == 1:
                    _a, _b = res
                    a, b = self.args
                    if a is _a:
                        return _b, _a
            
        return res

    invert = BinaryCondition.invert
    
    def _subs_sliced(self, old, new, **hints):        
        lhs, rhs = self.args
        if lhs.is_random and lhs.is_symbol and not rhs.is_random and old.is_random and old.is_symbol and not new.is_random:
            if lhs == old:
                return self

        return Relational._subs_sliced(self, old, new, **hints)
    
    def _subs(self, old, new, **kwargs):
        lhs, rhs = self.args
        if lhs.is_random and lhs.is_symbol:
            if new == lhs and rhs == old:
                if old == lhs.var or not rhs.is_random:
                    new = new.surrogate
                    return self.func(lhs, new, evaluate=False)
            elif old == lhs:
                if not rhs.is_random and not rhs.is_Surrogate:
                    return self

        try:
            return super(Equal, self)._subs(old, new, **kwargs)
        except Exception as e:
            if e.args[0] == 'empty slices':
                if lhs.is_Sliced and rhs.is_Sliced:
                    if lhs.catch_exception(old, new) and rhs.catch_exception(old, new):
                        return S.true
            raise e

    def _try_to_substitute(self, other, new):
        if not other.is_Equal:
            return
        
        if self.lhs != other.lhs:
            return
        
        rhs = self.rhs
        _rhs = other.rhs
        
        if rhs == _rhs:
            ...
        
        if rhs.is_Surrogate:
            if rhs.arg.var == _rhs:
                return new._subs(_rhs, rhs)

    @classmethod
    def sub_class_key(cls):
        return -6


Eq = Equal


class Unequal(Relational):
    """An unequal relation between two objects.

    Explanation
    ===========

    Represents that two objects are not equal.  If they can be shown to be
    definitively equal, this will reduce to False; if definitively unequal,
    this will reduce to True.  Otherwise, the relation is maintained as an
    Unequal object.

    Examples
    ========

    >>> from sympy import Ne
    >>> from sympy.abc import x, y
    >>> Ne(y, x+x**2)
    Ne(y, x**2 + x)

    See Also
    ========
    Equal

    Notes
    =====
    This class is not the same as the != operator.  The != operator tests
    for exact structural equality between two expressions; this class
    compares expressions mathematically.

    This class is effectively the inverse of Equal.  As such, it uses the
    same algorithms, including any available `_eval_Eq` methods.

    """
    rel_op = '!='

    invert_type = Equal
    __slots__ = ()

    def _sympystr(self, p):
        return 'Unequal(%s, %s)' % tuple(p._print(arg) for arg in self.args)

    def _lean(self, p):
        return '%s \N{NOT EQUAL TO} %s' % tuple(p._print(arg) for arg in self.args)

    def __new__(cls, lhs, rhs, **options):
        if options.pop('sympify', True):
            lhs = _sympify(lhs)
            rhs = _sympify(rhs)
        if options.pop('evaluate', global_parameters.evaluate):
            is_equal = Equal(lhs, rhs)
            if isinstance(is_equal, BooleanAtom):
                if 'plausible' in options:
                    if is_equal:
                        options['plausible'] = False
                    else:
                        options['plausible'] = None
                else:
                    return is_equal.invert().copy(**options)

        if options:
            from sympy.core.inference import Inference
            return Inference(Relational.__new__(cls, lhs, rhs), **options)

        return Relational.__new__(cls, lhs, rhs, **options)

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        return _sympify(lhs != rhs)

    @property
    def binary_symbols(self):
        if S.true in self.args or S.false in self.args:
            if self.lhs.is_Symbol:
                return {self.lhs}
            elif self.rhs.is_Symbol:
                return {self.rhs}
        return set()

    def _eval_simplify(self, **kwargs):
        # simplify as an equality
        eq = Equal(*self.args)._eval_simplify(**kwargs)
        if isinstance(eq, Equal):
            # send back Ne with the new args
            return self.func(*eq.args)
        return ~eq  # result of Ne is the negated Eq

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            arg = args[0]
            if isinstance(arg, Equal):
                eq = arg
                args = eq.args
                lhs = self.lhs.subs(*args, **kwargs)
                rhs = self.rhs.subs(*args, **kwargs)
                return self.func(lhs, rhs).simplify().overwrite(self)
            else:
                return self

        if all(isinstance(arg, Boolean) for arg in args):
            res = self
            for eq in args:
                res = res.subs(eq)
            return res

        return BinaryCondition.subs(self, *args, **kwargs)

    def simplify(self, deep=False, wrt=None, **kwargs):
        if deep or wrt is not None:
            return BinaryCondition.simplify(self, deep=True, wrt=wrt)

        lhs, rhs = self.args
        this = self.lhs.func.simplify_Unequal(self, lhs, rhs)
        if this is not None:
            return this.simplify()
             
        this = self.rhs.func.simplify_Unequal(self, rhs, lhs)
        if this is not None:
            return this
        
        return super(Unequal, self).simplify()

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_Or:
            return other.__and__(self)

        elif other.is_LessEqual:
            if set(self.args) == set(other.args):
                return Less(other.lhs, other.rhs)

        elif other.is_GreaterEqual:
            if set(self.args) == set(other.args):
                return Greater(other.lhs, other.rhs)

        elif isinstance(other, (Less, Greater)):
            if set(self.args) == set(other.args):
                return other

        elif other.is_Equal:
            if self.lhs == other.lhs:
                cond = Equal(self.rhs, other.rhs)
                if cond:
                    return S.false
                
                if cond == False:
                    return other

            elif self.lhs == other.rhs:
                cond = Equal(self.rhs, other.lhs)
                if cond:
                    return S.false

                if cond == False:
                    return other

        return Relational.__and__(self, other)

    def __truediv__(self, other, **kwargs):
        if other.is_Equal:
            if other.lhs.is_nonzero or other.rhs.is_nonzero:
                return self.func(self.lhs / other.lhs, self.rhs / other.rhs)
            return self
        else:
            if other.is_nonzero:
                return self.func((self.lhs / other).ratsimp(), (self.rhs / other).ratsimp())
            if other.is_zero:
                return self
            from sympy import Or
            return Or(Equal(other, 0), self.func((self.lhs / other).ratsimp(), (self.rhs / other).ratsimp()))

    def __mul__(self, other, **kwargs):
        if isinstance(other, Unequal):
            return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        
        return Relational.__mul__(self, other)

    def __or__(self, other):
        if other.is_LessEqual:
            if self.lhs == other.lhs and self.rhs <= other.rhs or \
            self.lhs == other.rhs and other.rhs <= self.rhs or \
            self.rhs == other.lhs and self.lhs <= other.rhs or \
            self.rhs == other.rhs and other.lhs <= self.rhs:
                return S.true
        elif other.is_GreaterEqual:
            if self.lhs == other.lhs and self.rhs >= other.rhs or \
            self.lhs == other.rhs and other.rhs >= self.rhs or \
            self.rhs == other.lhs and self.lhs >= other.rhs or \
            self.rhs == other.rhs and other.lhs >= self.rhs:
                return S.true
        elif other.is_Or:
            for cond in other.args:
                if cond.is_NotElement:
                    e, s = cond.args
                    if e == self.rhs and s._contains(self.lhs) == False or \
                    e == self.lhs and s._contains(self.rhs) == False:
                        return S.true
        elif other.is_NotElement:
            e, s = other.args
            if e == self.lhs:
                contains = s._contains(self.rhs)
                if contains == False:
                    return S.true
                elif contains == True:
                    return self

            elif e == self.rhs:
                contains = s._contains(self.lhs)
                if contains == False:
                    return S.true
                elif contains == True:
                    return self
            
        return Relational.__or__(self, other)

    def domain_conditioned(self, var):
        if ret := self.domain_conditioned_utility(var):
            a, solution, domain = ret
            return domain - {solution}

        lhs, rhs = self.args
        if lhs.is_Mod:
            if lhs.args[0] == var:
                d = lhs.args[1]
                if d > 0 and rhs >= 0 and rhs < d:
                    # x % d == t => x in Range(t, oo, d)
                    from sympy import Range, oo
                    domain = var.domain & self.domain_defined(var)
                    return domain - (Range(rhs, oo, d) | Range(rhs - d, -oo, -d))

        return BinaryCondition.domain_conditioned(self, var)
    
    of = Equal.of

    invert = BinaryCondition.invert

    @classmethod
    def sub_class_key(cls):
        return -5


Ne = Unequal
Equal.invert_type = Unequal


class Inequality(Relational):
    """Internal base class for all *Than types.

    Each subclass must implement _eval_relation to provide the method for
    comparing two real numbers.

    """
    __slots__ = ()

    def __new__(cls, lhs, rhs, **options):
        if options.pop('sympify', True):
            lhs = _sympify(lhs)
            rhs = _sympify(rhs)
        if options.pop('evaluate', global_parameters.evaluate):
            # First we invoke the appropriate inequality method of `lhs`
            # (e.g., `lhs.__lt__`).  That method will try to reduce to
            # boolean or raise an exception.  It may keep calling
            # superclasses until it reaches `Expr` (e.g., `Expr.__lt__`).
            # In some cases, `Expr` will just invoke us again (if neither it
            # nor a subclass was able to reduce to boolean or raise an
            # exception).  In that case, it must call us with
            # `evaluate=False` to prevent infinite recursion.
            r = cls._eval_relation(lhs, rhs)
            if r is not None and r.is_BooleanAtom:
                if 'plausible' in options:
                    if r:
                        options['plausible'] = None
                    else:
                        options['plausible'] = False
                else:
                    return r.copy(**options)

            # Note: not sure r could be None, perhaps we never take this
            # path?  In principle, could use this to shortcut out if a
            # class realizes the inequality cannot be evaluated further.

        # make a "non-evaluated" Expr for the inequality
        if options:
            from sympy.core.inference import Inference
            return Inference(Relational.__new__(cls, lhs, rhs), **options)
        
        return Relational.__new__(cls, lhs, rhs, **options)

    @classmethod
    def _eval_relation(cls, lhs, rhs, **options):
        val = cls._eval_fuzzy_relation(lhs, rhs)
        if val is None:
            return cls(lhs, rhs, evaluate=False)
        else:
            return _sympify(val)

    def __and__(self, other):
        if other.is_And:
            eqs = other.args
            for i, eq in enumerate(eqs):
                et = self & eq
                if et.is_And:
                    continue
                
                eqs = [*eqs]
                del eqs[i]
                return et & other.func(*eqs)
                        
        return Relational.__and__(self, other)


class _Greater(Inequality):
    """Not intended for general use

    _Greater is only used so that GreaterEqual and Greater may
    subclass it for the .gts and .lts properties.

    """
    __slots__ = ()

    def __and__(self, other):
        if isinstance(other, _Greater): 
            if self.lhs == other.lhs:
                from sympy import Max
                if self.func == other.func:
                    m = Max(self.rhs, other.rhs)
                    if m is self.rhs:
                        return self
                    if m is other.rhs:
                        return other
                
        elif isinstance(other, _Less):
            if self.rhs == other.rhs: 
                left = other.lhs
                left_open = isinstance(other, Less)
                
                right = self.lhs
                right_open = isinstance(self, Greater)
                if left_open:
                    if right_open:
                        ...
                    else:
                        if left >= right:
                            return S.false
                
        return Inequality.__and__(self, other)

    @property
    def gts(self):
        return self._args[0]

    @property
    def lts(self):
        return self._args[1]

    def limit(self, x, xlim, dir=1):
        """ Compute limit x->xlim.
        """
        return GreaterEqual(self.lhs.limit(x, xlim, dir), self.rhs.limit(x, xlim, dir), given=self, evaluate=False)


class _Less(Inequality):
    """Not intended for general use.

    _Less is only used so that LessEqual and Less may subclass it for
    the .gts and .lts properties.

    """
    __slots__ = ()

    @property
    def gts(self):
        return self._args[1]

    @property
    def lts(self):
        return self._args[0]

    def __and__(self, other):
        if isinstance(other, _Greater):
            if self.rhs == other.rhs: 
                left = self.lhs
                left_open = isinstance(self, Less)
                
                right = other.lhs
                right_open = isinstance(other, Greater)
                
                if left_open:
                    if right_open:
                        ...
                    else:
                        if left >= right:
                            return S.false
                        return Relational.__and__(self, other)
        elif isinstance(other, _Less):
            if self.lhs == other.lhs: 
                from sympy import Min
                if self.func == other.func:
                    m = Min(self.rhs, other.rhs)
                    if m is self.rhs:
                        return self
                    if m is other.rhs:
                        return other

        return Inequality.__and__(self, other)

    def limit(self, x, xlim, direction=True):
        """ Compute limit x->xlim.
        """
        return LessEqual(self.lhs.limit(x, xlim, direction), self.rhs.limit(x, xlim, direction), given=self, evaluate=False)


class GreaterEqual(_Greater):
    """Class representations of inequalities.

    Explanation
    ===========

    The ``*Than`` classes represent inequal relationships, where the left-hand
    side is generally bigger or smaller than the right-hand side.  For example,
    the GreaterEqual class represents an inequal relationship where the
    left-hand side is at least as big as the right side, if not bigger.  In
    mathematical notation:

    lhs >= rhs

    In total, there are four ``*Than`` classes, to represent the four
    inequalities:

    +-----------------+--------+
    |Class Name       | Symbol |
    +=================+========+
    |GreaterEqual      | (>=)   |
    +-----------------+--------+
    |LessEqual         | (<=)   |
    +-----------------+--------+
    |Greater| (>)    |
    +-----------------+--------+
    |Less   | (<)    |
    +-----------------+--------+

    All classes take two arguments, lhs and rhs.

    +----------------------------+-----------------+
    |Signature Example           | Math equivalent |
    +============================+=================+
    |GreaterEqual(lhs, rhs)       |   lhs >= rhs    |
    +----------------------------+-----------------+
    |LessEqual(lhs, rhs)          |   lhs <= rhs    |
    +----------------------------+-----------------+
    |Greater(lhs, rhs) |   lhs >  rhs    |
    +----------------------------+-----------------+
    |Less(lhs, rhs)    |   lhs <  rhs    |
    +----------------------------+-----------------+

    In addition to the normal .lhs and .rhs of Relations, ``*Than`` inequality
    objects also have the .lts and .gts properties, which represent the "less
    than side" and "greater than side" of the operator.  Use of .lts and .gts
    in an algorithm rather than .lhs and .rhs as an assumption of inequality
    direction will make more explicit the intent of a certain section of code,
    and will make it similarly more robust to client code changes:

    >>> from sympy import GreaterEqual, Greater
    >>> from sympy import LessEqual,    Less
    >>> from sympy import And, Ge, Gt, Le, Lt, Rel, S
    >>> from sympy.abc import x, y, z
    >>> from sympy.core.relational import Relational

    >>> e = GreaterEqual(x, 1)
    >>> e
    x >= 1
    >>> '%s >= %s is the same as %s <= %s' % (e.gts, e.lts, e.lts, e.gts)
    'x >= 1 is the same as 1 <= x'

    Examples
    ========

    One generally does not instantiate these classes directly, but uses various
    convenience methods:

    >>> for f in [Ge, Gt, Le, Lt]:  # convenience wrappers
    ...     print(f(x, 2))
    x >= 2
    x > 2
    x <= 2
    x < 2

    Another option is to use the Python inequality operators (>=, >, <=, <)
    directly.  Their main advantage over the Ge, Gt, Le, and Lt counterparts,
    is that one can write a more "mathematical looking" statement rather than
    littering the math with oddball function calls.  However there are certain
    (minor) caveats of which to be aware (search for 'gotcha', below).

    >>> x >= 2
    x >= 2
    >>> _ == Ge(x, 2)
    True

    However, it is also perfectly valid to instantiate a ``*Than`` class less
    succinctly and less conveniently:

    >>> Rel(x, 1, ">")
    x > 1
    >>> Relational(x, 1, ">")
    x > 1

    >>> Greater(x, 1)
    x > 1
    >>> GreaterEqual(x, 1)
    x >= 1
    >>> LessEqual(x, 1)
    x <= 1
    >>> Less(x, 1)
    x < 1

    Notes
    =====

    There are a couple of "gotchas" to be aware of when using Python's
    operators.

    The first is that what your write is not always what you get:

        >>> 1 < x
        x > 1

        Due to the order that Python parses a statement, it may
        not immediately find two objects comparable.  When "1 < x"
        is evaluated, Python recognizes that the number 1 is a native
        number and that x is *not*.  Because a native Python number does
        not know how to compare itself with a SymPy object
        Python will try the reflective operation, "x > 1" and that is the
        form that gets evaluated, hence returned.

        If the order of the statement is important (for visual output to
        the console, perhaps), one can work around this annoyance in a
        couple ways:

        (1) "sympify" the literal before comparison

        >>> S(1) < x
        1 < x

        (2) use one of the wrappers or less succinct methods described
        above

        >>> Lt(1, x)
        1 < x
        >>> Relational(1, x, "<")
        1 < x

    The second gotcha involves writing equality tests between relationals
    when one or both sides of the test involve a literal relational:

        >>> e = x < 1; e
        x < 1
        >>> e == e  # neither side is a literal
        True
        >>> e == x < 1  # expecting True, too
        False
        >>> e != x < 1  # expecting False
        x < 1
        >>> x < 1 != x < 1  # expecting False or the same thing as before
        Traceback (most recent call last):
        ...
        TypeError: cannot determine truth value of Relational

        The solution for this case is to wrap literal relationals in
        parentheses:

        >>> e == (x < 1)
        True
        >>> e != (x < 1)
        False
        >>> (x < 1) != (x < 1)
        False

    The third gotcha involves chained inequalities not involving
    '==' or '!='. Occasionally, one may be tempted to write:

        >>> e = x < y < z
        Traceback (most recent call last):
        ...
        TypeError: symbolic boolean expression has no truth value.

        Due to an implementation detail or decision of Python [1]_,
        there is no way for SymPy to create a chained inequality with
        that syntax so one must use And:

        >>> e = And(x < y, y < z)
        >>> type( e )
        And
        >>> e
        (x < y) & (y < z)

        Although this can also be done with the '&' operator, it cannot
        be done with the 'and' operarator:

        >>> (x < y) & (y < z)
        (x < y) & (y < z)
        >>> (x < y) and (y < z)
        Traceback (most recent call last):
        ...
        TypeError: cannot determine truth value of Relational

    .. [1] This implementation detail is that Python provides no reliable
       method to determine that a chained inequality is being built.
       Chained comparison operators are evaluated pairwise, using "and"
       logic (see
       http://docs.python.org/2/reference/expressions.html#notin). This
       is done in an efficient way, so that each object being compared
       is only evaluated once and the comparison can short-circuit. For
       example, ``1 > 2 > 3`` is evaluated by Python as ``(1 > 2) and (2
       > 3)``. The ``and`` operator coerces each side into a bool,
       returning the object itself when it short-circuits. The bool of
       the --Than operators will raise TypeError on purpose, because
       SymPy cannot determine the mathematical ordering of symbolic
       expressions. Thus, if we were to compute ``x > y > z``, with
       ``x``, ``y``, and ``z`` being Symbols, Python converts the
       statement (roughly) into these steps:

        (1) x > y > z
        (2) (x > y) and (y > z)
        (3) (GreaterThanObject) and (y > z)
        (4) (GreaterThanObject.__bool__()) and (y > z)
        (5) TypeError

       Because of the "and" added at step 2, the statement gets turned into a
       weak ternary statement, and the first object's __bool__ method will
       raise TypeError.  Thus, creating a chained inequality is not possible.

           In Python, there is no way to override the ``and`` operator, or to
           control how it short circuits, so it is impossible to make something
           like ``x > y > z`` work.  There was a PEP to change this,
           :pep:`335`, but it was officially closed in March, 2012.

    """
    __slots__ = ()

    rel_op = '>='

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__ge__(rhs))

    def inverse(self):
        if self.rhs.is_extended_positive:
            if self.lhs.is_extended_positive:
                return self.reversed_type(1 / self.lhs, 1 / self.rhs)
            from sympy.sets import Element, Interval
            return Element(1 / self.lhs, Interval(0, 1 / self.rhs, left_open=True))
        if self.rhs.is_extended_negative:
            if self.lhs.is_extended_negative:
                return self.reversed_type(1 / self.lhs, 1 / self.rhs)

        return self

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equal):
                args = eq.args
                return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))
            elif isinstance(eq, dict):
                if eq:
                    subs = self
                    for key, value in eq.items():
                        subs = subs._subs(key, value)
                    return subs
                else:
                    return self
            elif eq.is_Quantifier:
                return self.bfn(self.subs, eq)

            return self
        return BinaryCondition.subs(self, *args, **kwargs) 

    def __and__(self, other):
        if isinstance(other, GreaterEqual):
            if self.lhs == other.rhs:
                if other.lhs == self.rhs:
                    return Equal(*self.args)
                if other.lhs < self.rhs:
                    return S.false
            elif self.lhs == other.lhs:
                # x >= a, x >= b
                if self.rhs >= other.rhs:
                    return self
                if self.rhs <= other.rhs:
                    return other
                
        elif isinstance(other, LessEqual):
            if self.lhs == other.lhs:
                if self.rhs == other.rhs:
                    return Equal(*self.args)
                if other.rhs < self.rhs:
                    return S.false
        if isinstance(other, Less):
            if self.lhs == other.lhs:
                if self.rhs >= other.rhs:
                    return S.false
        elif isinstance(other, Greater):
            if self.lhs == other.lhs:
                if self.rhs <= other.rhs:
                    return other
#                 x >= 1 and x > 0
                if self.rhs > other.rhs:
                    return self
        elif isinstance(other, Unequal):
            if {*self.args} == {*other.args}:
                return Greater(self.lhs, self.rhs)            
        elif isinstance(other, Equal):
            if {*self.args} == {*other.args}:
                return other
        elif other.is_Element:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs:
                    if other.rhs.right_open:
                        if self.rhs >= other.rhs.stop:
                            return S.false
                    else:
                        if self.rhs > other.rhs.stop:
                            return S.false
        elif other.is_NotElement:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs:
                    if other.rhs.left_open and self.rhs > other.rhs.start or \
                    not other.rhs.left_open and self.rhs >= other.rhs.start:
                        if other.rhs.right_open:
                            if self.lhs < other.rhs.stop:
                                return S.false
                        else:
                            if self.lhs <= other.rhs.stop:
                                return S.false
                
        return _Greater.__and__(self, other)

    def __mul__(self, other, **kwargs):
        if isinstance(other, GreaterEqual):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given={self, other})
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonpositive:
                    return self.reversed_type(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, Greater):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonpositive:
                    return self.reversed_type(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, Less):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonpositive:
                    return LessEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonnegative:
                    return GreaterEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
                
        return Relational.__mul__(self, other)

    def __or__(self, other):
        if other.is_Equal:
            if {*other.args} == {*self.args}:
                return self
            
            if self.lhs == other.lhs and self.lhs.is_integer and self.rhs == other.rhs + 1:
#                 x >= 3 and x == 2 => x >= 2
                return self.func(*other.args)
        elif other.is_Unequal:
            if other.lhs == self.lhs and other.rhs >= self.rhs or \
            other.lhs == self.rhs and self.rhs >= other.rhs or \
            other.rhs == self.lhs and other.lhs >= self.rhs or \
            other.rhs == self.rhs and self.lhs >= other.rhs:
                return S.true
        elif other.is_Less:
#             x >= -1 | x < 0
            if self.lhs == other.lhs:
                if self.rhs <= other.rhs:
                    return S.true
                
        elif other.is_LessEqual:
            if self.lhs == other.lhs:
                if self.rhs <= other.rhs:
                    return S.true
                # x >= 1 and x <= 0
                if self.lhs.is_integer and self.rhs <= other.rhs + 1:
                    return S.true
            
        elif other.is_GreaterEqual:
            if self.lhs == other.lhs:
                # x >= a or x >= a + 1
                if self.rhs >= other.rhs:
                    return other
                if self.rhs <= other.rhs:
                    return self
            
        elif other.is_Greater:
            if self.lhs == other.lhs:
                # x >= 1 or x > 2
                if self.rhs > other.rhs:
                    return other
                if self.rhs <= other.rhs:
                    return self
                
        return Relational.__or__(self, other)

    def simplify(self, deep=False, wrt=None, **kwargs):
        if self.lhs.is_Maxima:
            maximize = self.lhs
            if maximize.expr == self.rhs:
                if all(len(limit) == 1 for limit in maximize.limits):
                    return S.true
        return Relational.simplify(self, deep=deep, wrt=wrt)
    
    def _sympystr(self, p):
        return '%s >= %s' % tuple(p._print(arg) for arg in self.args)

    def _lean(self, p):
        return '%s \N{GREATER-THAN OR EQUAL TO} %s' % tuple(p._print(arg) for arg in self.args)

    def of(self, cls):
        res = Boolean.of(self, cls)
        if res is None:
            if cls.is_GreaterEqual:
                a, b = cls.args
                cls = Basic.__new__(LessEqual, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)
            elif cls.is_LessEqual:
                a, b = cls.args
                cls = Basic.__new__(GreaterEqual, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)         
            
        return res

    def domain_conditioned(self, var):
        if ret := self.domain_conditioned_utility(var):
            a, solution, domain = ret
            from sympy import Interval
            if a.is_extended_negative:
                return domain & Interval(S.NegativeInfinity, solution)
            
            if a.is_extended_positive:
                return domain & Interval(solution, S.Infinity)

        return BinaryCondition.domain_conditioned(self, var)

    @classmethod
    def sub_class_key(cls):
        return -1


Ge = GreaterEqual


class LessEqual(_Less):
    __doc__ = GreaterEqual.__doc__
    __slots__ = ()

    rel_op = '<='

    def __add__(self, other, **kwargs):
        other = sympify(other)
        if isinstance(other, (Less, LessEqual)):
            return other.func(self.lhs + other.lhs, self.rhs + other.rhs, given=[self, other]).simplify()
        else:
            return Relational.__add__(self, other)

    def inverse(self):
        if self.rhs.is_extended_positive:
            if self.lhs.is_extended_positive:
                return self.reversed_type(1 / self.lhs, 1 / self.rhs)
        if self.rhs.is_extended_negative:
            if self.lhs.is_extended_negative:
                return self.reversed_type(1 / self.lhs, 1 / self.rhs)
            from sympy.sets import Element, Interval
            return Element(1 / self.lhs, Interval(1 / self.rhs, 0, right_open=True))

        return self

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__le__(rhs))

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equal):
                args = eq.args
                return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))
            elif isinstance(eq, dict):
                res = self
                for k, v in eq.items():
                    res = res._subs(k, v)
                return res
            elif eq.is_Quantifier:
                return self.bfn(self.subs, eq)

            return self

        if all(isinstance(arg, Relational) for arg in args):
            free_symbols = self.free_symbols
            f = self.lhs - self.rhs
            given = []
            for eq in args:
                if eq.plausible:
                    given.append(eq)
                old, new = eq.args
                if old in free_symbols:
                    domain = old.domain & old.domain_conditioned(eq)
                    if domain != old.domain:
                        _old = Symbol(old.name, domain=domain)
                        f = f.subs(old, _old)
                else:
                    return self

            maxi = f.max()
            if self.plausible:
                return LessEqual(maxi, 0, imply=self, given=given)
            return self

        old, new = args
       
        if not isinstance(old, Symbol):
            lhs = self.lhs.subs(old, new)
            rhs = self.rhs.subs(old, new)

            g = self.lhs - self.rhs
            _g = lhs - rhs
            if _g < g:
                return Less(lhs, rhs, given=self)
            if _g <= g:
                return LessEqual(lhs, rhs, given=self)

            if _g > g:
                return GreaterEqual(lhs, rhs, given=self)
            if _g >= g:
                return Greater(lhs, rhs, given=self)
        return BinaryCondition.subs(self, *args, **kwargs)

    def __and__(self, other):
        if other.is_LessEqual:
            if self.lhs == other.rhs:
                if other.lhs == self.rhs:
                    return Equal(self.lhs, self.rhs)
                if other.lhs > self.rhs:
                    return S.false
            elif self.lhs == other.lhs:
                # x <= a, x <= b
                if self.rhs <= other.rhs:
                    return self
                
                if self.rhs >= other.rhs:
                    return other
                
        elif other.is_Less:
            if self.lhs == other.lhs:
#                 x <= 1 and x < 0
                if self.rhs >= other.rhs:
                    return other
#                 x <= 0 and x < 1
                if self.rhs < other.rhs:
                    return self

            elif self.lhs == other.rhs:
                if other.lhs >= self.rhs:
                    return S.false
        elif other.is_GreaterEqual:
            if self.lhs == other.lhs:
                if other.rhs == self.rhs:
                    return Equal(self.lhs, self.rhs)
                if other.rhs > self.rhs:
                    return S.false
        elif other.is_Greater:
            if self.lhs == other.lhs:
                if other.rhs >= self.rhs:
                    return S.false
            elif self.rhs == other.rhs:
                if other.lhs <= self.lhs:
                    return S.false
                
        elif other.is_Element:
            if other.rhs.is_Range:
                if self.lhs == other.lhs:
                    if self.rhs < other.rhs.start:
                        return S.false

                    return other.func(self.lhs, other.rhs.func(S.NegativeInfinity, self.rhs + 1) & other.rhs).simplify()
            elif other.rhs.is_Interval:
                if self.lhs == other.lhs:
                    if other.rhs.left_open:
                        if self.rhs <= other.rhs.start:
                            return S.false
                    else:
                        if self.rhs < other.rhs.start:
                            return S.false

                    return other.func(self.lhs, other.rhs.func(S.NegativeInfinity, self.rhs) & other.rhs).simplify()
                
        elif other.is_Unequal:
            if {*self.args} == {*other.args}:
                return Less(*self.args)
            
        elif other.is_NotElement:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs:
                    if other.rhs.right_open and self.rhs < other.rhs.stop or \
                    not other.rhs.right_open and self.rhs <= other.rhs.stop:
                        if other.rhs.left_open:
                            if self.lhs > other.rhs.start:
                                return S.false
                        else:
                            if self.lhs >= other.rhs.start:
                                return S.false
            
        return _Less.__and__(self, other)

    def __mul__(self, other, **kwargs):
        if isinstance(other, LessEqual):
            if self.lhs.is_extended_nonnegative: 
                if other.lhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            elif self.rhs.is_extended_nonpositive:
                if other.rhs.is_extended_nonpositive:
                    return self.reversed_type(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, Greater):
            if self.lhs.is_extended_nonnegative: 
                if other.lhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            elif self.rhs.is_extended_nonpositive:
                if other.rhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        
        return Relational.__mul__(self, other)

    def __or__(self, other):
        if other.is_Equal:
            if {*other.args} == {*self.args}:
                return self
            if self.lhs == other.lhs and self.lhs.is_integer and self.rhs + 1 == other.rhs:
#                 x <= 3 and x == 4 => x >= 4
                return self.func(*other.args)
            
        elif other.is_Unequal:
            if other.lhs == self.lhs and other.rhs <= self.rhs or \
            other.lhs == self.rhs and self.rhs <= other.rhs or \
            other.rhs == self.lhs and other.lhs <= self.rhs or \
            other.rhs == self.rhs and self.lhs <= other.rhs:
                return S.true
            
        elif other.is_Greater:
#             x <= 1 | x > 0
            if self.lhs == other.lhs:
                if self.rhs >= other.rhs:
                    return S.true

        elif other.is_GreaterEqual:
#             x <= 1 | x > 0
            if self.lhs == other.lhs:
                if self.rhs >= other.rhs:
                    return S.true
                # x <= 0 and x >= 1
                if self.lhs.is_integer:
                    if self.rhs + 1 >= other.rhs:
                        return S.true
                    
        elif other.is_LessEqual:
            if self.lhs == other.lhs:
                # x <= a or x < a + 1
                if self.rhs <= other.rhs:
                    return other
                if self.rhs >= other.rhs:
                    return self
                
        elif other.is_Less:
            if self.lhs == other.lhs:
                # x <= a or x < a + 1
                if self.rhs < other.rhs:
                    return other
                if self.rhs >= other.rhs:
                    return self
            
        return Relational.__or__(self, other)

    def simplify(self, deep=False, wrt=None, **kwargs):
        if self.lhs.is_Minima:
            minimize = self.lhs
            if minimize.expr == self.rhs:
                if all(len(limit) == 1 for limit in minimize.limits):
                    return S.true
        return Relational.simplify(self, deep=deep, wrt=wrt)

    def _sympystr(self, p):
        # \N{LESS-THAN OR EQUAL TO}
        # LESS-THAN OVER EQUAL TO
        return '%s <= %s' % tuple(p._print(arg) for arg in self.args)

    def _lean(self, p):
        return '%s \N{LESS-THAN OR EQUAL TO} %s' % tuple(p._print(arg) for arg in self.args)

    def of(self, cls):
        res = Boolean.of(self, cls)
        if res is None:
            if cls.is_LessEqual:
                a, b = cls.args
                cls = Basic.__new__(GreaterEqual, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return a, b
            elif cls.is_GreaterEqual:
                args = cls.args
                if isinstance(args, property):
                    b, a = self.args
                    return a, b
                else:
                    a, b = args
                    cls = Basic.__new__(LessEqual, b, a)
                    res = Boolean.of(self, cls)
                    if b.is_Number:
                        return res
                    if isinstance(res, tuple):
                        b, a = res
                        return a, b
            
        return res

    def domain_conditioned(self, var):
        if ret := self.domain_conditioned_utility(var):
            a, solution, domain = ret
            from sympy import Interval
            if a.is_extended_negative:
                return domain & Interval(solution, S.Infinity)
            
            if a.is_extended_positive:
                return domain & Interval(S.NegativeInfinity, solution)

        return BinaryCondition.domain_conditioned(self, var)
    
    @classmethod
    def sub_class_key(cls):
        return -2


Le = LessEqual


class Greater(_Greater):
    __doc__ = GreaterEqual.__doc__
    __slots__ = ()

    rel_op = '>'
    invert_type = LessEqual

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__gt__(rhs))

    def __add__(self, other, **kwargs):
        other = sympify(other)
        if other.is_Equal: 
            return self.func(self.lhs + other.lhs, self.rhs + other.rhs, **other.add_sub_assumptions(self)).simplify()
        elif other.is__Greater:
            return self.func(self.lhs + other.lhs, self.rhs + other.rhs, given=[self, other]).simplify()
        else:
            return self.func(self.lhs + other, self.rhs + other)

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equal):
                args = eq.args
                return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))
            elif isinstance(eq, dict):
                if eq:
                    subs = self
                    for key, value in eq.items():
                        subs = subs._subs(key, value)
                    return subs
                else:
                    return self
            elif eq.is_Quantifier:
                return self.bfn(self.subs, eq)

            return self
        
        if all(isinstance(arg, Boolean) for arg in args):
            res = self
            for eq in args:
                res = res.subs(eq)
            return res

        return BinaryCondition.subs(self, *args, **kwargs)
            
    def is_positive_relationship(self):
        if self.rhs.is_zero:
            return self.lhs

    def __and__(self, other):
        if isinstance(other, Less):
            if self.lhs == other.lhs:
                if other.rhs <= self.rhs: 
                    return S.false
#                 x > a and x < b
                if self.lhs.is_integer:
                    # x in (b; a)
                    from sympy import Range
                    if not Range(self.rhs, other.rhs, left_open=True, right_open=True):
                        return S.false
                
        elif isinstance(other, LessEqual):
            if self.lhs == other.lhs:
                if other.rhs <= self.rhs: 
                    return S.false
            elif self.rhs == other.rhs:
                if other.lhs >= self.lhs: 
                    return S.false
                    
        elif isinstance(other, Unequal):
            if set(self.args) == set(other.args):
                return self
        elif isinstance(other, Equal):
            if set(self.args) == set(other.args):
                return S.false
            
        elif isinstance(other, _Greater):
            if self.lhs == other.lhs:
                if self.rhs >= other.rhs:
                    return self
#                 x > 0 and x >= 1
                if self.rhs < other.rhs:
                    return other
                
#                 x > a and a >= x + 1
            if self.rhs == other.lhs:
                if self.lhs <= other.rhs:
                    return S.false
                 
        elif other.is_Element:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs:
                    if self.rhs >= other.rhs.stop:
                            return S.false
                
        elif other.is_NotElement:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs: 
                    if self.rhs >= other.rhs.start:
                        if other.rhs.right_open:
                            if self.lhs < other.rhs.stop:
                                return S.false
                        else:
                            if self.lhs <= other.rhs.stop:
                                return S.false
                               
        return _Greater.__and__(self, other)

    def __or__(self, other):
        if isinstance(other, Unequal):
            if self.lhs == other.lhs:
                if self.rhs == other.rhs: 
                    return other
                if self.lhs <= other.rhs:
                    return (self.lhs < other.rhs) | self
            elif self.lhs == other.rhs:
                if self.rhs == other.lhs:
                    return other
                if self.lhs <= other.lhs:
                    return (self.lhs < other.lhs) | self
        elif isinstance(other, Equal):
            if set(self.args) == set(other.args):
                return GreaterEqual(self.lhs, self.rhs)
            
        elif isinstance(other, Less):
            if self.lhs == other.lhs:
                if other.rhs > self.rhs:
                    return S.true
                if other.rhs == self.rhs:
                    return Unequal(*self.args)
            if self.rhs == other.rhs:
                if self.lhs > other.lhs:
                    return S.true
        elif isinstance(other, Greater):
            if self.lhs == other.rhs:
                if other.lhs > self.rhs:
                    return S.true
                if other.lhs == self.rhs:
                    return Unequal(*self.args)
                
            if self.rhs == other.lhs:
                if self.lhs > other.rhs:
                    return S.true
                
            if self.lhs == other.lhs:
                # x > a or x > a + 1
                if self.rhs >= other.rhs:
                    return other
                if self.rhs <= other.rhs:
                    return self
                
        elif isinstance(other, LessEqual):
            if self.lhs == other.lhs:
                if self.rhs <= other.rhs:
                    return S.true
            if self.rhs == other.rhs:
                if other.lhs <= self.lhs:
                    return S.true
        elif isinstance(other, GreaterEqual):
            if self.lhs == other.rhs:
                if self.rhs <= other.lhs:
                    return S.true
            if self.rhs == other.lhs:
                if other.rhs <= self.lhs:
                    return S.true
            if self.lhs == other.lhs:
#                 x > 2 or x >= 1
                if self.rhs >= other.rhs:
                    return other
                
                if self.rhs < other.rhs:
                    return self
            
        return _Greater.__or__(self, other)

    def __mul__(self, other, **kwargs):
        if isinstance(other, Greater):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonpositive:
                    return self.reversed_type(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, GreaterEqual):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonnegative:
                    return GreaterEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonpositive:
                    return LessEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, LessEqual):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonpositive:
                    return LessEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonnegative:
                    return GreaterEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, Less):
            if self.rhs.is_extended_nonnegative: 
                if other.rhs.is_extended_nonpositive:
                    return Less(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            if self.lhs.is_extended_nonpositive: 
                if other.lhs.is_extended_nonnegative:
                    return Greater(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        return Relational.__mul__(self, other)

    def of(self, cls):
        res = Boolean.of(self, cls)
        if res is None:
            if cls.is_Greater:
                a, b = cls.args
                cls = Basic.__new__(Less, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)
            elif cls.is_Less:
                a, b = cls.args
                cls = Basic.__new__(Greater, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)         
            
        return res

    def domain_conditioned(self, var):
        if ret := self.domain_conditioned_utility(var):
            a, solution, domain = ret
            from sympy import Interval
            if a.is_extended_negative:
                return domain & Interval(S.NegativeInfinity, solution, right_open=True)
            elif a.is_extended_positive:
                return domain & Interval(solution, S.Infinity, left_open=True)

        return BinaryCondition.domain_conditioned(self, var)

    @classmethod
    def sub_class_key(cls):
        return -3


Gt = Greater
LessEqual.invert_type = Greater


class Less(_Less):
    __doc__ = GreaterEqual.__doc__
    __slots__ = ()

    rel_op = '<'
    invert_type = GreaterEqual

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__lt__(rhs))

    def __add__(self, other, **kwargs):
        other = sympify(other)
        if isinstance(other, Equal):
            return self.func(self.lhs + other.lhs, self.rhs + other.rhs, **other.add_sub_assumptions(self)).simplify()
        elif other.is__Less:
            return self.func(self.lhs + other.lhs, self.rhs + other.rhs, given=[self, other]).simplify()
        else:
            return self.func(self.lhs + other, self.rhs + other)

    def subs(self, *args, **kwargs):
        from sympy.simplify import simplify
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equal):
                args = eq.args
                return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))
            elif isinstance(eq, dict):
                if eq:
                    subs = self
                    for key, value in eq.items():
                        subs = subs._subs(key, value)
                    return subs
                else:
                    return self
            elif eq.is_Quantifier:
                return self.bfn(self.subs, eq)

            return self
        return BinaryCondition.subs(self, *args, **kwargs)

    def is_positive_relationship(self):
        if self.lhs.is_zero:
            return self.rhs

    def __and__(self, other):
        if isinstance(other, Less):
            if self.rhs == other.lhs:
                if self.lhs <= other.rhs: 
                    return S.false
                
        elif isinstance(other, GreaterEqual):
            if self.lhs == other.lhs:
                if self.rhs <= other.rhs:
                    return S.false
                if self.lhs.is_integer and self.rhs == other.rhs + 1:
                    return Equal(*other.args)                
        elif isinstance(other, Greater):
            # x < a and x > b
            if self.lhs == other.lhs:
                if self.rhs <= other.rhs: 
                    return S.false
                if self.lhs.is_integer:
                    # x in (b; a)
                    from sympy import Range
                    if not Range(other.rhs, self.rhs, left_open=True, right_open=True):
                        return S.false
                
        elif isinstance(other, Unequal):
            if set(self.args) == set(other.args):
                return self
        elif isinstance(other, Equal):
            if set(self.args) == set(other.args):
                return S.false
        elif isinstance(other, _Less):
            if self.lhs == other.lhs:
#                 x < 0 and x <= 1
                if self.rhs <= other.rhs:
                    return self
#                 x < 1 and x <= 0
                if self.rhs > other.rhs:
                    return other
            if self.rhs == other.lhs:
#                 x < a and a < x - 1
                if self.lhs >= other.rhs:
                    return S.false
        
        elif other.is_Element:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs:
                    if self.rhs <= other.rhs.start:
                        return S.false
        elif other.is_NotElement:
            if other.rhs.is_Range or other.rhs.is_Interval:
                if self.lhs == other.lhs: 
                    if self.rhs <= other.rhs.stop:
                        if other.rhs.left_open:
                            if self.lhs > other.rhs.start:
                                return S.false
                        else:
                            if self.lhs >= other.rhs.start:
                                return S.false

        return _Less.__and__(self, other)

    def __or__(self, other):
        if isinstance(other, Unequal):
            if self.lhs == other.lhs:
                if self.rhs == other.rhs: 
                    return other
                if self.lhs >= other.rhs:
                    return (self.lhs > other.rhs) | self
            elif self.lhs == other.rhs:
                if self.rhs == other.lhs:
                    return other
                if self.lhs >= other.lhs:
                    return (self.lhs > other.lhs) | self
        elif isinstance(other, Equal):
            if set(self.args) == set(other.args):
                return LessEqual(self.lhs, self.rhs)
            
        elif isinstance(other, Greater):
            if self.lhs == other.lhs:
                if self.rhs > other.rhs:
                    return S.true
                if other.rhs == self.rhs:
                    return Unequal(*self.args)
            if self.rhs == other.rhs:
                if other.lhs > self.lhs:
                    return S.true
        elif isinstance(other, Less):
            if self.lhs == other.rhs:
                if self.rhs > other.lhs:
                    return S.true
                if other.lhs == self.rhs:
                    return Unequal(*self.args)
                
            if self.rhs == other.lhs:
                if other.rhs > self.lhs:
                    return S.true
            
            if self.lhs == other.lhs:
                # x < a or x < a + 1
                if self.rhs <= other.rhs:
                    return other
                if self.rhs >= other.rhs:
                    return self
            
        elif isinstance(other, GreaterEqual):
            if self.lhs == other.lhs:
                if self.rhs >= other.rhs:
                    return S.true
            if self.rhs == other.rhs:
                if other.lhs >= self.lhs:
                    return S.true

        elif isinstance(other, LessEqual):
            if self.lhs == other.rhs:
                if self.rhs >= other.lhs:
                    return S.true
            if self.rhs == other.lhs:
                if other.rhs >= self.lhs:
                    return S.true

            if self.lhs == other.lhs:
#                 t < 1, t <= 2
                if self.rhs <= other.rhs:
                    return other
                if self.rhs > other.rhs:
                    return self
                
                                              
        return _Less.__or__(self, other)

    def __mul__(self, other, **kwargs):
        other = sympify(other)
        if isinstance(other, Less):
            if self.lhs.is_extended_nonnegative: 
                if other.lhs.is_extended_nonnegative:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            elif self.rhs.is_extended_nonpositive:
                if other.rhs.is_extended_nonpositive:
                    return self.reversed_type(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
        elif isinstance(other, GreaterEqual):
            if self.lhs.is_extended_nonnegative: 
                if other.lhs.is_extended_nonpositive:
                    return GreaterEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            elif self.rhs.is_extended_nonpositive:
                if other.rhs.is_extended_nonnegative:
                    return LessEqual(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])          
        elif isinstance(other, Greater):
            if self.lhs.is_extended_nonnegative: 
                if other.lhs.is_extended_nonpositive:
                    return Greater(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])
            elif self.rhs.is_extended_nonpositive:
                if other.rhs.is_extended_nonnegative:
                    return Less(self.lhs * other.lhs, self.rhs * other.rhs, given=[self, other])          
        elif not other.is_Boolean:
            if other.is_extended_positive:
                return self.func(self.lhs * other, self.rhs * other)
            if other.is_extended_negative:
                return self.reversed_type(self.lhs * other, self.rhs * other)
            elif other.is_extended_nonnegative:
                return LessEqual(self.lhs * other, self.rhs * other, given=self)
            elif other.is_extended_nonpositive:
                return GreaterEqual(self.lhs * other, self.rhs * other, given=self)
            return self

        return Relational.__mul__(self, other)

    def of(self, cls):
        res = Boolean.of(self, cls)
        if res is None:
            if cls.is_Less:
                a, b = cls.args
                cls = Basic.__new__(Greater, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)
            elif cls.is_Greater:
                a, b = cls.args
                cls = Basic.__new__(Less, b, a)
                res = Boolean.of(self, cls)
                if b.is_Number:
                    return res
                if isinstance(res, tuple):
                    b, a = res
                    return (a, b)         
            
        return res

    def domain_conditioned(self, var):
        if ret := self.domain_conditioned_utility(var):
            a, solution, domain = ret
            from sympy import Interval
            if a.is_extended_negative:
                return domain & Interval(solution, S.Infinity, left_open=True)
            elif a.is_extended_positive:
                return domain & Interval(S.NegativeInfinity, solution, right_open=True)

        return BinaryCondition.domain_conditioned(self, var)

    @classmethod
    def sub_class_key(cls):
        return -4


Lt = Less
GreaterEqual.invert_type = Less

Ge.reversed_type = Le
Lt.reversed_type = Gt
Le.reversed_type = Ge
Ne.reversed_type = Ne
Eq.reversed_type = Eq
Gt.reversed_type = Lt

# A class-specific (not object-specific) data item used for a minor speedup.
# It is defined here, rather than directly in the class, because the classes
# that it references have not been defined until now (e.g. Less).
Relational.ValidRelationOperator = {
    None: Equal,
    '==': Equal,
    'eq': Equal,
    '!=': Unequal,
    '<>': Unequal,
    'ne': Unequal,
    '>=': GreaterEqual,
    'ge': GreaterEqual,
    '<=': LessEqual,
    'le': LessEqual,
    '>': Greater,
    'gt': Greater,
    '<': Less,
    'lt': Less,
}


@dispatch(Expr, Expr)
def _eval_is_ge(lhs, rhs):
    return None


@dispatch(Basic, Basic)
def _eval_is_eq(lhs, rhs):
    return None


@dispatch(Tuple, Expr)  # type: ignore
def _eval_is_eq(lhs, rhs):  # noqa:F811
    return False


@dispatch(Tuple, AppliedUndef)  # type: ignore
def _eval_is_eq(lhs, rhs):  # noqa:F811
    return None


@dispatch(Tuple, Symbol)  # type: ignore
def _eval_is_eq(lhs, rhs):  # noqa:F811
    return None


@dispatch(Tuple, Tuple)  # type: ignore
def _eval_is_eq(lhs, rhs):  # noqa:F811
    if len(lhs) != len(rhs):
        return False

    return fuzzy_and(fuzzy_bool(is_eq(s, o)) for s, o in zip(lhs, rhs))


def is_lt(lhs, rhs):
    """Fuzzy bool for lhs is strictly less than rhs.

    See the docstring for is_ge for more
    """
    return fuzzy_not(is_ge(lhs, rhs))


def is_gt(lhs, rhs):
    """Fuzzy bool for lhs is strictly greater than rhs.

    See the docstring for is_ge for more
    """
    return fuzzy_not(is_le(lhs, rhs))


def is_le(lhs, rhs):
    """Fuzzy bool for lhs is less than or equal to rhs.
    is_gt calls is_lt
    See the docstring for is_ge for more
    """
    return is_ge(rhs, lhs)


from sympy.core.expr import _n2
def is_ge(lhs, rhs):
    """
    Fuzzy bool for lhs is greater than or equal to rhs.

    Parameters
    ==========

    lhs: Expr
        The left-hand side of the expression, must be sympified,
        and an instance of expression. Throws an exception if
        lhs is not an instance of expression.

    rhs: Expr
        The right-hand side of the expression, must be sympified
        and an instance of expression. Throws an exception if
        lhs is not an instance of expression.

    Returns
    =======

    Expr : True if lhs is greater than or equal to rhs, false is
        lhs is less than rhs, and None if the comparison between
        lhs and rhs is indeterminate.

    The four comparison functions ``is_le``, ``is_lt``, ``is_ge``, and ``is_gt`` are
    each implemented in terms of ``is_ge`` in the following way:

    is_ge(x, y) := is_ge(x, y)
    is_le(x, y) := is_ge(y, x)
    is_lt(x, y) := fuzzy_not(is_ge(x, y))
    is_gt(x, y) = fuzzy_not(is_ge(y, x))

    To maintain these equivalences in fuzzy logic it is important that in cases where
    either x or y is non-real all comparisons will give None.

    InEquality classes, such as Lt, Gt, etc. Use one of is_ge, is_le, etc.
    To implement comparisons with ``Gt(a, b)`` or ``a > b`` etc for an ``Expr`` subclass
    it is only necessary to define a dispatcher method for ``_eval_is_ge`` like

    Examples
    ========


    >>> is_ge(S(2), S(0))
    True
    >>> is_ge(S(0), S(2))
    False
    >>> is_ge(S(0), x)

    >>> is_gt(S(2), S(0))
    True
    >>> is_gt(S(0), S(2))
    False
    >>> is_lt(S(0), S(2))
    True
    >>> is_lt(S(2), S(0))
    False

   """
    if not (isinstance(lhs, Expr) and isinstance(rhs, Expr)):
        raise TypeError("Can only compare inequalities with Expr")

    retval = _eval_is_ge(lhs, rhs)

    if retval is not None:
        return retval

    n2 = _n2(lhs, rhs)
    if n2 is not None:
        # use float comparison for infinity.
        # otherwise get stuck in infinite recursion
        if n2 in (S.Infinity, S.NegativeInfinity):
            n2 = float(n2)
        return _sympify(n2 >= 0)
    if lhs.is_extended_real and rhs.is_extended_real:
        if (lhs.is_infinite and lhs.is_extended_positive) or (rhs.is_infinite and rhs.is_extended_negative):
            return True
        diff = lhs - rhs
        if diff is not S.NaN:
            rv = diff.is_extended_nonnegative
            if rv is not None:
                return rv


def is_neq(lhs, rhs):
    """Fuzzy bool for lhs does not equal rhs.

    See the docstring for is_eq for more
    """
    return fuzzy_not(is_eq(lhs, rhs))


def is_eq(lhs, rhs):
    """
    Fuzzy bool representing mathematical equality between lhs and rhs.

    Parameters
    ==========

    lhs: Expr
        The left-hand side of the expression, must be sympified.

    rhs: Expr
        The right-hand side of the expression, must be sympified.

    Returns
    =======

    True if lhs is equal to rhs, false is lhs is not equal to rhs, and
    None if the comparison between lhs and rhs is indeterminate.

    Explanation
    ===========

    This function is intended to give a relatively fast determination and deliberately does not attempt slow
    calculations that might help in obtaining a determination of True or False in more difficult cases.

    InEquality classes, such as Lt, Gt, etc. Use one of is_ge, is_le, etc.
    To implement comparisons with ``Gt(a, b)`` or ``a > b`` etc for an ``Expr`` subclass
    it is only necessary to define a dispatcher method for ``_eval_is_ge`` like

    Examples
    ========



    >>> is_eq(S(0), S(0))
    True
    >>> Eq(0, 0)
    True
    >>> is_neq(S(0), S(0))
    False
    >>> is_eq(S(0), S(2))
    False
    >>> Eq(0, 2)
    False
    >>> is_neq(S(0), S(2))
    True
    >>> is_eq(S(0), x)

    >>> Eq(S(0), x)
    Eq(0, x)



    """
    from sympy.core.add import Add
    from sympy.functions.elementary.complexes import arg
    from sympy.simplify.simplify import clear_coefficients
    from sympy.utilities.iterables import sift

    # here, _eval_Eq is only called for backwards compatibility
    # new code should use is_eq with multiple dispatch as
    # outlined in the docstring
    for side1, side2 in (lhs, rhs), (rhs, lhs):
        eval_func = getattr(side1, '_eval_Eq', None)
        if eval_func is not None:
            retval = eval_func(side2)
            if retval is not None:
                return retval

    retval = _eval_is_eq(lhs, rhs)
    if retval is not None:
        return retval

    if dispatch(type(lhs), type(rhs)) != dispatch(type(rhs), type(lhs)):
        retval = _eval_is_eq(rhs, lhs)
        if retval is not None:
            return retval

    # retval is still None, so go through the equality logic
    # If expressions have the same structure, they must be equal.
    if lhs == rhs:
        return True  # e.g. True == True
    elif all(isinstance(i, BooleanAtom) for i in (rhs, lhs)):
        return False  # True != False
    elif not (lhs.is_Symbol or rhs.is_Symbol) and (
        isinstance(lhs, Boolean) != 
        isinstance(rhs, Boolean)):
        return False  # only Booleans can equal Booleans

    if lhs.is_infinite or rhs.is_infinite:
        if fuzzy_xor([lhs.is_infinite, rhs.is_infinite]):
            return False
        if fuzzy_xor([lhs.is_extended_real, rhs.is_extended_real]):
            return False
        if fuzzy_and([lhs.is_extended_real, rhs.is_extended_real]):
            return fuzzy_xor([lhs.is_extended_positive, fuzzy_not(rhs.is_extended_positive)])

        # Try to split real/imaginary parts and equate them
        I = S.ImaginaryUnit

        def split_real_imag(expr):
            real_imag = lambda t: (
                'real' if t.is_extended_real else
                'imag' if (I * t).is_extended_real else None)
            return sift(Add.make_args(expr), real_imag)

        lhs_ri = split_real_imag(lhs)
        if not lhs_ri[None]:
            rhs_ri = split_real_imag(rhs)
            if not rhs_ri[None]:
                eq_real = Eq(Add(*lhs_ri['real']), Add(*rhs_ri['real']))
                eq_imag = Eq(I * Add(*lhs_ri['imag']), I * Add(*rhs_ri['imag']))
                return fuzzy_and(map(fuzzy_bool, [eq_real, eq_imag]))

        # Compare e.g. zoo with 1+I*oo by comparing args
        arglhs = arg(lhs)
        argrhs = arg(rhs)
        # Guard against Eq(nan, nan) -> Falsesymp
        if not (arglhs == S.NaN and argrhs == S.NaN):
            return fuzzy_bool(Eq(arglhs, argrhs))

    if all(isinstance(i, Expr) for i in (lhs, rhs)):
        # see if the difference evaluates
        diff = lhs - rhs
        z = diff.is_zero
        if z is not None:
            if z is False and diff.is_commutative:  # issue 10728
                return False
            if z:
                return True

        n2 = _n2(lhs, rhs)
        if n2 is not None:
            return _sympify(n2 == 0)

        # see if the ratio evaluates
        n, d = diff.as_numer_denom()
        rv = None
        if n.is_zero:
            rv = d.is_nonzero
        elif n.is_finite:
            if d.is_infinite:
                rv = True
            elif n.is_zero is False:
                rv = d.is_infinite
                if rv is None:
                    # if the condition that makes the denominator
                    # infinite does not make the original expression
                    # True then False can be returned
                    l, r = clear_coefficients(d, S.Infinity)
                    args = [_.subs(l, r) for _ in (lhs, rhs)]
                    if args != [lhs, rhs]:
                        rv = fuzzy_bool(Eq(*args))
                        if rv is True:
                            rv = None
        elif any(a.is_infinite for a in Add.make_args(n)):
            # (inf or nan)/x != 0
            rv = False
        if rv is not None:
            return rv
