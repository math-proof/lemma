"""Base class for all the objects in SymPy"""
from collections import defaultdict
from collections.abc import Mapping
from itertools import chain, zip_longest

from .assumptions import BasicMeta, ManagedProperties
from .cache import cacheit
from .sympify import _sympify, sympify, SympifyError
from .compatibility import iterable, ordered
from ._print_helpers import Printable

from inspect import getmro


def as_Basic(expr):
    """Return expr as a Basic instance using strict sympify
    or raise a TypeError; this is just a wrapper to _sympify,
    raising a TypeError instead of a SympifyError."""
    from sympy.utilities.misc import func_name
    try:
        return _sympify(expr)
    except SympifyError:
        raise TypeError(
            'Argument must be a Basic object, not `%s`' % func_name(
            expr))


class Basic(Printable, metaclass=ManagedProperties):
    """
    Base class for all SymPy objects.

    Notes and conventions
    =====================

    1) Always use ``.args``, when accessing parameters of some instance:

    >>> from sympy import cot
    >>> from sympy.abc import x, y

    >>> cot(x).args
    (x,)

    >>> cot(x).args[0]
    x

    >>> (x*y).args
    (x, y)

    >>> (x*y).args[1]
    y


    2) Never use internal methods or variables (the ones prefixed with ``_``):

    >>> cot(x)._args    # do not use this, use cot(x).args instead
    (x,)


    3)  By "SymPy object" we mean something that can be returned by
        ``sympify``.  But not all objects one encounters using SymPy are
        subclasses of Basic.  For example, mutable objects are not:

        >>> from sympy import Basic, Matrix, sympify
        >>> A = Matrix([[1, 2], [3, 4]]).as_mutable()
        >>> isinstance(A, Basic)
        False

        >>> B = sympify(A)
        >>> isinstance(B, Basic)
        True
    """
    __slots__ = ('_mhash',  # hash value
                 '_args',  # arguments
                 '_assumptions',
                 '_domain_defined'
                )

    # To be overridden with True in the appropriate subclasses
    is_number = False
    is_symbol = False
   
    is_Punctured = False
    
    is_ConditionSet = False
    
    is_bool = False
    
    is_Matrix = False
    
    is_set = False
    
    is_infinitesimal = False

    is_Integral = False
    
    is_Inference = False
    # Wanted is used in expression: Product + {Sum[Sum]}
    is_Wanted = False
    
    is_IndexedOperator = False
    
    is_super_complex = True
    
    is_FunctionClass = False
    
    is_elementwise = False
    
    is_distribution = False

    def definition_set(self, dependency):
        from sympy.core.symbol import Symbol

        hashset = set()
        for arg in preorder_traversal(self):
            if isinstance(arg, Symbol) and arg.definition is not None:
                if arg not in hashset:
                    hashset.add(arg)   
                    if arg not in dependency: 
                        dependency[arg] = arg.definition.definition_set(dependency)                    
            
        return hashset
        
    def condition_set(self):
        ...

    def intersection_sets(self, b):
        ...

    def preorder_traversal(self):
        from sympy import preorder_traversal
        return preorder_traversal(self)
    
    def __and__(self, other):
        """Overloading for & operator"""
        if self.is_set:
            return self.intersect(other)

        if not other.is_bool and self.is_random and other.is_random:
            return self & other.as_boolean()

        rhs = None
        if other.is_And:
            rhs = tuple(other._argset)
        elif other.is_Or:
            _self = self.invert()
            if _self in other._argset:
                args = set(other._argset)
                args.remove(_self)
                rhs = (other.func(*args),)

        if rhs is None:
            rhs = (other,)
            
        from sympy.logic.boolalg import And
        return And(self, *rhs)

    __rand__ = __and__

    def __or__(self, other):
        if self.is_bool and other.is_bool: 
            from sympy.logic.boolalg import Or
            """Overloading for |"""
            return Or(self, other)
        from sympy.stats.rv import given
        return given(self, other)        

    def __ror__ (self, other):
        if self.is_bool and other.is_bool:
            return other.__or__(self)
        
        if self.is_set:
            return self.__or__(other)
        
        from sympy.stats.rv import given
        return given(other, self)

    def union_sets(self, b):
        ...

    def __new__(cls, *args, **kwargs):
        obj = object.__new__(cls)
#         obj._assumptions = cls.default_assumptions
        obj._assumptions = cls.default_assumptions.copy()
        obj._mhash = None  # will be set by __hash__ method.

        obj._args = args  # all items in args must be Basic objects

        for name, value in kwargs.items():
            if name not in obj._assumptions:
                if value is not None:
                    obj._assumptions[name] = value
                    
        return obj

    def copy(self, **kwargs):
        return self.func(*self.args, **kwargs)

    @property
    def set(self):
        from sympy.sets.sets import FiniteSet
        return FiniteSet(self)

    def __reduce_ex__(self, proto):
        """ Pickling support."""
        return type(self), self.__getnewargs__(), self.__getstate__()

    def __getnewargs__(self):
        return self.args

    def __getstate__(self):
        return None

    def __setstate__(self, state):
        for k, v in state.items():
            setattr(self, k, v)

    def __hash__(self):
        # hash cannot be cached using cache_it because infinite recurrence
        # occurs as hash is needed for setting cache dictionary keys
        h = self._mhash
        if h is None:
            h = hash((type(self).__name__,) + self._hashable_content())
            self._mhash = h
        return h

    def _hashable_content(self):
        """Return a tuple of information about self that can be used to
        compute the hash. If a class defines additional attributes,
        like ``name`` in Symbol, then this method should be updated
        accordingly to return such relevant attributes.

        Defining more than _hashable_content is necessary if __eq__ has
        been defined by a class. See note about this in Basic.__eq__."""
        return self._args

    @property
    def assumptions0(self):
        """
        Return object `type` assumptions.

        For example:

          Symbol('x', real=True)
          Symbol('x', integer=True)

        are different objects. In other words, besides Python type (Symbol in
        this case), the initial assumptions are also forming their typeinfo.

        Examples
        ========

        >>> from sympy import Symbol
        >>> from sympy.abc import x
        >>> x.assumptions0
        {'commutative': True}
        >>> x = Symbol("x", positive=True)
        >>> x.assumptions0
        {'commutative': True, 'complex': True, 'extended_negative': False,
         'extended_nonnegative': True, 'extended_nonpositive': False,
         'extended_nonzero': True, 'extended_positive': True, 'extended_real':
         True, 'finite': True, 'hermitian': True, 'imaginary': False,
         'infinite': False, 'negative': False, 'nonnegative': True,
         'nonpositive': False, 'nonzero': True, 'positive': True, 'real':
         True, 'zero': False}
        """
        return {}

    def compare(self, other):
        """
        Return -1, 0, 1 if the object is smaller, equal, or greater than other.

        Not in the mathematical sense. If the object is of a different type
        from the "other" then their classes are ordered according to
        the sorted_classes list.

        Examples
        ========

        >>> from sympy.abc import x, y
        >>> x.compare(y)
        -1
        >>> x.compare(x)
        0
        >>> y.compare(x)
        1

        """
        # all redefinitions of __cmp__ method should start with the
        # following lines:
        if self is other:
            return 0
        n1 = self.__class__
        n2 = other.__class__
        c = (n1.gt(n2)) - (n1.lt(n2))
        if c:
            return c
        #
        st = self._hashable_content()
        ot = other._hashable_content()
        c = (len(st) > len(ot)) - (len(st) < len(ot))
        if c:
            return c
        for l, r in zip(st, ot):
            l = Basic(*l) if isinstance(l, frozenset) else l
            r = Basic(*r) if isinstance(r, frozenset) else r
            if isinstance(l, Basic):
                c = l.compare(r)
            else:
                c = self._compare_relation(l > r, l < r)
            if c:
                return c
        return 0

    @staticmethod
    def _compare_relation(gt, lt):
        if isinstance(gt, Basic):
            return gt.compare(lt) if isinstance(lt, Basic) else 1
        else:
            return -1 if isinstance(lt, Basic) else gt - lt

    @staticmethod
    def _compare_pretty(a, b):
        from sympy.series.order import Order
        if isinstance(a, Order) and not isinstance(b, Order):
            return 1
        if not isinstance(a, Order) and isinstance(b, Order):
            return -1

        if a.is_Rational and b.is_Rational:
            l = a.p * b.q
            r = b.p * a.q
            return (l > r) - (l < r)
        else:
            from sympy.core.symbol import Wild
            p1, p2, p3 = Wild("p1"), Wild("p2"), Wild("p3")
            r_a = a.match(p1 * p2 ** p3)
            if r_a and p3 in r_a:
                a3 = r_a[p3]
                r_b = b.match(p1 * p2 ** p3)
                if r_b and p3 in r_b:
                    b3 = r_b[p3]
                    c = Basic.compare(a3, b3)
                    if c != 0:
                        return c

        return Basic.compare(a, b)

    @classmethod
    def fromiter(cls, args, **assumptions):
        """
        Create a new object from an iterable.

        This is a convenience function that allows one to create objects from
        any iterable, without having to convert to a list or tuple first.

        Examples
        ========

        >>> from sympy import Tuple
        >>> Tuple.fromiter(i for i in range(5))
        (0, 1, 2, 3, 4)

        """
        return cls(*tuple(args), **assumptions)

    @classmethod
    def class_key(cls):
        """Nice order of classes. """
        return 5, 0, cls.__name__

    @cacheit
    def sort_key(self, order=None):
        """
        Return a sort key.

        Examples
        ========

        >>> from sympy.core import S, I

        >>> sorted([S(1)/2, I, -I], key=lambda x: x.sort_key())
        [1/2, -I, I]

        >>> S("[x, 1/x, 1/x**2, x**2, x**(1/2), x**(1/4), x**(3/2)]")
        [x, 1/x, x**(-2), x**2, sqrt(x), x**(1/4), x**(3/2)]
        >>> sorted(_, key=lambda x: x.sort_key())
        [x**(-2), 1/x, x**(1/4), sqrt(x), x, x**(3/2), x**2]

        """

        # XXX: remove this when issue 5169 is fixed
        def inner_key(arg):
            if isinstance(arg, Basic):
                return arg.sort_key(order)
            else:
                return arg

        args = self._sorted_args
        args = len(args), tuple(arg.class_key() for arg in args), tuple(inner_key(arg) for arg in args)
        return self.class_key(), args, S.One.sort_key(), S.One

    def __eq__(self, other):
        """Return a boolean indicating whether a == b on the basis of
        their symbolic trees.

        This is the same as a.compare(b) == 0 but faster.

        Notes
        =====

        If a class that overrides __eq__() needs to retain the
        implementation of __hash__() from a parent class, the
        interpreter must be told this explicitly by setting __hash__ =
        <ParentClass>.__hash__. Otherwise the inheritance of __hash__()
        will be blocked, just as if __hash__ had been explicitly set to
        None.

        References
        ==========

        from http://docs.python.org/dev/reference/datamodel.html#object.__hash__
        """
        if self is other:
            return True

        tself = type(self)
        tother = type(other)
        if tself is not tother:
            try:
                other = _sympify(other)
                tother = type(other)
            except SympifyError:
                return NotImplemented

            # As long as we have the ordering of classes (sympy.core),
            # comparing types will be slow in Python 2, because it uses
            # __cmp__. Until we can remove it
            # (https://github.com/sympy/sympy/issues/4269), we only compare
            # types in Python 2 directly if they actually have __ne__.
            if type(tself).__ne__ is not type.__ne__:
                if tself != tother:
                    return False
            elif tself is not tother:
                return False

        return self._hashable_content() == other._hashable_content()

    def __ne__(self, other):
        """``a != b``  -> Compare two symbolic trees and see whether they are different

        this is the same as:

        ``a.compare(b) != 0``

        but faster
        """
        return not self == other

    def structurally_equal(self, other):
        if other.func != self.func or len(self.args) != len(other.args):
            return False
        for x, y in zip(self.args, other.args):
            if not x.structurally_equal(y):
                return False
        return True

# precondition, self and other are structurally equal!
    def _dummy_eq(self, other):
        if len(self.args) != len(other.args) or self.func != other.func:
            return False

        for x, y in zip(self.args, other.args):
            if not x._dummy_eq(y):
                return False
            
        kwargs = self.kwargs
        _kwargs = other.kwargs
        if len(kwargs) != len(_kwargs):
            return False
        
        for key in kwargs:
            value = kwargs[key]
            _value = _kwargs.get(key)
            if value != _value:
                return False

        return True

    def dummy_eq(self, other, symbol=None):
        """
        Compare two expressions and handle dummy symbols.

        Examples
        ========

        >>> from sympy import Dummy
        >>> from sympy.abc import x, y

        >>> u = Dummy('u')

        >>> (u**2 + 1).dummy_eq(x**2 + 1)
        True
        >>> (u**2 + 1) == (x**2 + 1)
        False

        >>> (u**2 + y).dummy_eq(x**2 + y, x)
        True
        >>> (u**2 + y).dummy_eq(x**2 + y, y)
        False

        """
        return self == other or self.structurally_equal(other) and self._dummy_eq(other)
    
    # Note, we always use the default ordering (lex) in __str__ and __repr__,
    # regardless of the global setting.  See issue 5487.
    def __repr__(self):
        """Method to return the string representation.

        Return the expression as a string.
        """
        from sympy.printing import sstr
        return sstr(self, order=None)

    def __str__(self):
        from sympy.printing import sstr
        return sstr(self, order=None)

    # We don't define _repr_png_ here because it would add a large amount of
    # data to any notebook containing SymPy expressions, without adding
    # anything useful to the notebook. It can still enabled manually, e.g.,
    # for the qtconsole, with init_printing().
    def _repr_latex_(self):
        """
        IPython/Jupyter LaTeX printing

        To change the behavior of this (e.g., pass in some settings to LaTeX),
        use init_printing(). init_printing() will also enable LaTeX printing
        for built in numeric types like ints and container types that contain
        SymPy objects, like lists and dictionaries of expressions.
        """
        from sympy.printing.latex import latex
        s = latex(self, mode='plain')
        return "$\\displaystyle %s$" % s

    _repr_latex_orig = _repr_latex_

    def atoms(self, *types):
        """Returns the atoms that form the current object.

        By default, only objects that are truly atomic and can't
        be divided into smaller pieces are returned: symbols, numbers,
        and number symbols like I and pi. It is possible to request
        atoms of any type, however, as demonstrated below.

        Examples
        ========

        >>> from sympy import I, pi, sin
        >>> from sympy.abc import x, y
        >>> (1 + x + 2*sin(y + I*pi)).atoms()
        {1, 2, I, pi, x, y}

        If one or more types are given, the results will contain only
        those types of atoms.

        >>> from sympy import Number, NumberSymbol, Symbol
        >>> (1 + x + 2*sin(y + I*pi)).atoms(Symbol)
        {x, y}

        >>> (1 + x + 2*sin(y + I*pi)).atoms(Number)
        {1, 2}

        >>> (1 + x + 2*sin(y + I*pi)).atoms(Number, NumberSymbol)
        {1, 2, pi}

        >>> (1 + x + 2*sin(y + I*pi)).atoms(Number, NumberSymbol, I)
        {1, 2, I, pi}

        Note that I (imaginary unit) and zoo (complex infinity) are special
        types of number symbols and are not part of the NumberSymbol class.

        The type can be given implicitly, too:

        >>> (1 + x + 2*sin(y + I*pi)).atoms(x) # x is a Symbol
        {x, y}

        Be careful to check your assumptions when using the implicit option
        since ``S(1).is_Integer = True`` but ``type(S(1))`` is ``One``, a special type
        of sympy atom, while ``type(S(2))`` is type ``Integer`` and will find all
        integers in an expression:

        >>> from sympy import S
        >>> (1 + x + 2*sin(y + I*pi)).atoms(S(1))
        {1}

        >>> (1 + x + 2*sin(y + I*pi)).atoms(S(2))
        {1, 2}

        Finally, arguments to atoms() can select more than atomic atoms: any
        sympy type (loaded in core/__init__.py) can be listed as an argument
        and those types of "atoms" as found in scanning the arguments of the
        expression recursively:

        >>> from sympy import Function, Mul
        >>> from sympy.core.function import AppliedUndef
        >>> f = Function('f')
        >>> (1 + f(x) + 2*sin(y + I*pi)).atoms(Function)
        {f(x), sin(y + I*pi)}
        >>> (1 + f(x) + 2*sin(y + I*pi)).atoms(AppliedUndef)
        {f(x)}

        >>> (1 + x + 2*sin(y + I*pi)).atoms(Mul)
        {I*pi, 2*sin(y + I*pi)}

        """
        if types:
            types = tuple(
                [t if isinstance(t, type) else type(t) for t in types])
        else:
            types = (Atom,)
        result = set()
        for expr in preorder_traversal(self):
            if isinstance(expr, types):
                result.add(expr)

        return result

    @property
    def free_symbols(self):
        return self._eval_free_symbols()

    @property
    def random_symbols(self):
        return self._eval_random_symbols()

    @staticmethod
    def merge_symbols(v, s):
        if s:
            from sympy import Range
            if v.is_Symbol:
                if s_deleted := {t for t in s if (t.is_Sliced or t.is_Indexed) and t.base == v}:
                    s -= s_deleted

            elif v.is_Indexed:
                if v.base in s:
                    return
                x, *indices = v.args
                if len(indices) > 1:
                    ...
                else:
                    i, = indices
                    for t in s:
                        if t.is_Sliced and t.base == x:
                            indices = t.indices
                            if len(indices) > 1:
                                continue
                            
                            (a, b), = indices
                            if i == a - 1:
                                a = i
                            elif i == b:
                                b += 1
                            else:
                                if Range(a, b).conditionally_contains(i):
                                    return
                                continue
    
                            s.remove(t)
                            s.add(x[a:b])
                            return
                        
            elif v.is_Sliced:
                if v.base in s:
                    return
                x, *indices = v.args
                if len(indices) > 1:
                    ...
                else:
                    start, stop, step = indices[0].slice_args
                    if step == 1:
                        for t in s:
                            if t.is_Indexed:
                                base, *indices = t.args
                                if base == x:
                                    ...
                                elif x.is_Indexed and base == x.base:
                                    if base[indices[0]] == x:
                                        base = base[indices[0]]
                                        indices = indices[1:]
                                    else:
                                        continue
                                else:
                                    continue

                                if len(indices) > 1:
                                    continue
    
                                i, = indices
                                if i == start - 1:
                                    start = i
                                elif i == stop:
                                    stop += 1
                                else:
                                    if Range(start, stop).conditionally_contains(i):
                                        s.remove(t)
                                    break
        
                                s.remove(t)
                                s.add(x[start:stop])
                                return
                            
                            if t.is_Sliced and t.base == x:
                                t_indices = t.indices
                                if len(t_indices) > 1:
                                    continue
                                
                                t_start, t_stop, t_step = t.indices[0].slice_args
                                if t_step != 1:
                                    continue
                                
                                if start <= t_start and t_stop <= stop:
                                    s.remove(t)
                                    s.add(v)
                                    return
                                
                                if t_start <= start and stop <= t_stop:
                                    return
                                
        s.add(v)
        
    @cacheit
    def _eval_random_symbols(self):
        s = set()
        for v in self.yield_random_symbols():
            Basic.merge_symbols(v, s)
        return s
    
    def effective_variable(self, variable):
        s = set()
        for v in self.yield_effective_variable(variable):
            Basic.merge_symbols(v, s)
        return s
    
    def yield_random_symbols(self):
        if self.is_symbol:
            if self.is_random:
                yield self
                
        elif self.is_PDF:
            ...
        else:
            if hasattr(self, '_argset'):
                args = self._argset
            else:
                args = self.args

            for arg in args:
                yield from arg.yield_random_symbols()

    def yield_effective_variable(self, variable):
        if self.is_symbol:
            if (definition := self.definition) is None:
                if self.is_random:
                    ...
                elif self._has(variable):
                    if variable.is_Symbol:
                        if self.is_Indexed:
                            if self.base == variable:
                                yield self
                            else:
                                for arg in self.args:
                                    yield from arg.yield_effective_variable(variable)

                            return

                    yield self
            else:
                yield from definition.yield_effective_variable(variable)
        else:
            if hasattr(self, '_argset'):
                args = self._argset
            else:
                args = self.args

            for arg in args:
                yield from arg.yield_effective_variable(variable)

    @cacheit
    def _eval_free_symbols(self):
        """Return from the atoms of self those which are free symbols.

        For most expressions, all symbols are free symbols. For some classes
        this is not true. e.g. Integrals use Symbols for the dummy variables
        which are bound variables, so Integral has a method to return all
        symbols except those. Derivative keeps track of symbols with respect
        to which it will perform a derivative; those are
        bound variables, too, so it has its own free_symbols method.

        Any other method that uses bound variables should implement a
        free_symbols method."""
        return set().union(*[a.free_symbols for a in self.args])

    @property
    def expr_free_symbols(self):
        from sympy.utilities.exceptions import SymPyDeprecationWarning
        SymPyDeprecationWarning(feature="expr_free_symbols method",
                                issue=21494,
                                deprecated_since_version="1.9").warn()
        return set()

    def as_dummy(self):
        """Return the expression with any objects having structurally
        bound symbols replaced with unique, canonical symbols within
        the object in which they appear and having only the default
        assumption for commutativity being True. When applied to a
        symbol a new symbol having only the same commutativity will be
        returned.

        Examples
        ========

        >>> from sympy import Integral, Symbol
        >>> from sympy.abc import x
        >>> r = Symbol('r', real=True)
        >>> Integral(r, (r, x)).as_dummy()
        Integral(_0, (_0, x))
        >>> _.variables[0].is_real is None
        True
        >>> r.as_dummy()
        _r

        Notes
        =====

        Any object that has structurally bound variables should have
        a property, `bound_symbols` that returns those symbols
        appearing in the object.
        """

        def can(x):
            d = {i: i.as_dummy() for i in x.bound_symbols}
            # mask free that shadow bound
            x = x.subs(d)
            c = x.canonical_variables
            # replace bound
            x = x.xreplace(c)
            # undo masking
            x = x.xreplace(dict((v, k) for k, v in d.items()))
            return x

        return self.replace(
            lambda x: hasattr(x, 'bound_symbols'),
            lambda x: can(x))

    @property
    def canonical_variables(self):
        """Return a dictionary mapping any variable defined in
        ``self.bound_symbols`` to Symbols that do not clash
        with any free symbols in the expression.

        Examples
        ========

        >>> from sympy import Lambda
        >>> from sympy.abc import x
        >>> Lambda(x, 2*x).canonical_variables
        {x: _0}
        """
        from sympy.core.symbol import Symbol
        from sympy.utilities.iterables import numbered_symbols
        if not hasattr(self, 'bound_symbols'):
            return {}
        dums = numbered_symbols('_')
        reps = {}
        v = self.bound_symbols
        from sympy.tensor.indexed import Sliced
        if isinstance(v, (Sliced, Symbol)):
            v = [v]
        # this free will include bound symbols that are not part of
        # self's bound symbols
        free = set([i.name for i in self.atoms(Symbol) - set(v)])
        for v in v:
            d = next(dums)
            if v.is_Symbol:
                while v.name == d.name or d.name in free:
                    d = next(dums)

            kwargs = v.type.dict
            if v.shape:
                kwargs['shape'] = v.shape
            
            d = Symbol(d.name, **kwargs)
            assert v.type == d.type

            reps[v] = d
        return reps

    def rcall(self, *args):
        """Apply on the argument recursively through the expression tree.

        This method is used to simulate a common abuse of notation for
        operators. For instance in SymPy the the following will not work:

        ``(x+Lambda(y, 2*y))(z) == x+2*z``,

        however you can use

        >>> from sympy import Lambda
        >>> from sympy.abc import x, y, z
        >>> (x + Lambda(y, 2*y)).rcall(z)
        x + 2*z
        """
        return Basic._recursive_call(self, args)

    @staticmethod
    def _recursive_call(expr_to_call, on_args):
        """Helper for rcall method."""
        from sympy import Symbol

        def the_call_method_is_overridden(expr):
            for cls in getmro(type(expr)):
                if '__call__' in cls.__dict__:
                    return cls != Basic

        if callable(expr_to_call) and the_call_method_is_overridden(expr_to_call):
            if isinstance(expr_to_call, Symbol):  # XXX When you call a Symbol it is
                return expr_to_call  # transformed into an UndefFunction
            else:
                return expr_to_call(*on_args)
        elif expr_to_call.args:
            args = [Basic._recursive_call(
                sub, on_args) for sub in expr_to_call.args]
            return type(expr_to_call)(*args)
        else:
            return expr_to_call

    def is_hypergeometric(self, k):
        from sympy.simplify import hypersimp
        from sympy.functions import Piecewise
        if self.has(Piecewise):
            return None
        return hypersimp(self, k) is not None

    @property
    def is_comparable(self):
        """Return True if self can be computed to a real number
        (or already is a real number) with precision, else False.

        Examples
        ========

        >>> from sympy import exp_polar, pi, I
        >>> (I*exp_polar(I*pi/2)).is_comparable
        True
        >>> (I*exp_polar(I*pi*2)).is_comparable
        False

        A False result does not mean that `self` cannot be rewritten
        into a form that would be comparable. For example, the
        difference computed below is zero but without simplification
        it does not evaluate to a zero with precision:

        >>> e = 2**pi*(1 + 2**pi)
        >>> dif = e - e.expand()
        >>> dif.is_comparable
        False
        >>> dif.n(2)._prec
        1

        """
        is_extended_real = self.is_extended_real
        if is_extended_real == False:
            return False
        if not self.is_number:
            return False
        # don't re-eval numbers that are already evaluated since
        # this will create spurious precision
        n, i = [p.evalf(2) if not p.is_Number else p
            for p in self.as_real_imag()]
        if not (i.is_Number and n.is_Number):
            return False
        if i:
            # if _prec = 1 we can't decide and if not,
            # the answer is False because numbers with
            # imaginary parts can't be compared
            # so return False
            return False
        else:
            return n._prec != 1

    @property
    def func(self):
        """
        The top-level function in an expression.

        The following should hold for all objects::

            >> x == x.func(*x.args)

        Examples
        ========

        >>> from sympy.abc import x
        >>> a = 2*x
        >>> a.func
        <class 'sympy.core.mul.Mul'>
        >>> a.args
        (2, x)
        >>> a.func(*a.args)
        2*x
        >>> a == a.func(*a.args)
        True

        """
        return self.__class__

    @property
    def args(self):
        """Returns a tuple of arguments of 'self'.

        Examples
        ========

        >>> from sympy import cot
        >>> from sympy.abc import x, y

        >>> cot(x).args
        (x,)

        >>> cot(x).args[0]
        x

        >>> (x*y).args
        (x, y)

        >>> (x*y).args[1]
        y

        Notes
        =====

        Never use self._args, always use self.args.
        Only use _args in __new__ when creating a new function.
        Don't override .args() from Basic (so that it's easy to
        change the interface in the future if needed).
        """
        return self._args

    @property
    def kwargs(self):
        # return hyper parameter of this object
        return {}
    
    @property
    def arg(self):
        return self._args[0]

    @property
    def _sorted_args(self):
        """
        The same as ``args``.  Derived classes which don't fix an
        order on their arguments should override this method to
        produce the sorted representation.
        """
        return self.args

    def as_poly(self, *gens, **args):
        """Converts ``self`` to a polynomial or returns ``None``.

        >>> from sympy import sin
        >>> from sympy.abc import x, y

        >>> print((x**2 + x*y).as_poly())
        Poly(x**2 + x*y, x, y, domain='ZZ')

        >>> print((x**2 + x*y).as_poly(x, y))
        Poly(x**2 + x*y, x, y, domain='ZZ')

        >>> print((x**2 + sin(y)).as_poly(x, y))
        None

        """
        from sympy.polys import Poly, PolynomialError

        try:
            poly = Poly(self, *gens, **args)

            if not poly.is_Poly:
                return None
            else:
                return poly
        except PolynomialError:
            return None

    def as_content_primitive(self, radical=False, clear=True):
        """A stub to allow Basic args (like Tuple) to be skipped when computing
        the content and primitive components of an expression.

        See Also
        ========

        sympy.core.expr.Expr.as_content_primitive
        """
        return S.One, self

    def subs(self, *args, **kwargs):
        """
        Substitutes old for new in an expression after sympifying args.

        `args` is either:
          - two arguments, e.g. foo.subs(old, new)
          - one iterable argument, e.g. foo.subs(iterable). The iterable may be
             o an iterable container with (old, new) pairs. In this case the
               replacements are processed in the order given with successive
               patterns possibly affecting replacements already made.
             o a dict or set whose key/value items correspond to old/new pairs.
               In this case the old/new pairs will be sorted by op count and in
               case of a tie, by number of args and the default_sort_key. The
               resulting sorted list is then processed as an iterable container
               (see previous).

        If the keyword ``simultaneous`` is True, the subexpressions will not be
        evaluated until all the substitutions have been made.

        Examples
        ========

        >>> from sympy import pi, exp, limit, oo
        >>> from sympy.abc import x, y
        >>> (1 + x*y).subs(x, pi)
        pi*y + 1
        >>> (1 + x*y).subs({x:pi, y:2})
        1 + 2*pi
        >>> (1 + x*y).subs([(x, pi), (y, 2)])
        1 + 2*pi
        >>> reps = [(y, x**2), (x, 2)]
        >>> (x + y).subs(reps)
        6
        >>> (x + y).subs(reversed(reps))
        x**2 + 2

        >>> (x**2 + x**4).subs(x**2, y)
        y**2 + y

        To replace only the x**2 but not the x**4, use xreplace:

        >>> (x**2 + x**4).xreplace({x**2: y})
        x**4 + y

        To delay evaluation until all substitutions have been made,
        set the keyword ``simultaneous`` to True:

        >>> (x/y).subs([(x, 0), (y, 0)])
        0
        >>> (x/y).subs([(x, 0), (y, 0)], simultaneous=True)
        nan

        This has the added feature of not allowing subsequent substitutions
        to affect those already made:

        >>> ((x + y)/y).subs({x + y: y, y: x + y})
        1
        >>> ((x + y)/y).subs({x + y: y, y: x + y}, simultaneous=True)
        y/(x + y)

        In order to obtain a canonical result, unordered iterables are
        sorted by count_op length, number of arguments and by the
        default_sort_key to break any ties. All other iterables are left
        unsorted.

        >>> from sympy import sqrt, sin, cos
        >>> from sympy.abc import a, b, c, d, e

        >>> A = (sqrt(sin(2*x)), a)
        >>> B = (sin(2*x), b)
        >>> C = (cos(2*x), c)
        >>> D = (x, d)
        >>> E = (exp(x), e)

        >>> expr = sqrt(sin(2*x))*sin(exp(x)*x)*cos(2*x) + sin(2*x)

        >>> expr.subs(dict([A, B, C, D, E]))
        a*c*sin(d*e) + b

        The resulting expression represents a literal replacement of the
        old arguments with the new arguments. This may not reflect the
        limiting behavior of the expression:

        >>> (x**3 - 3*x).subs({x: oo})
        nan

        >>> limit(x**3 - 3*x, x, oo)
        oo

        If the substitution will be followed by numerical
        evaluation, it is better to pass the substitution to
        evalf as

        >>> (1/x).evalf(subs={x: 3.0}, n=21)
        0.333333333333333333333

        rather than

        >>> (1/x).subs({x: 3.0}).evalf(21)
        0.333333333333333314830

        as the former will ensure that the desired level of precision is
        obtained.

        See Also
        ========
        replace: replacement capable of doing wildcard-like matching,
                 parsing of match, and conditional replacements
        xreplace: exact node replacement in expr tree; also capable of
                  using matching rules
        sympy.core.evalf.EvalfMixin.evalf: calculates the given formula to a desired level of precision

        """
        from sympy.core.containers import Dict
        from sympy.utilities import default_sort_key

        unordered = False

        if len(args) == 1:
            sequence = args[0]
            if isinstance(sequence, set):
                unordered = True
            elif isinstance(sequence, (Dict, Mapping)):
                unordered = True
                sequence = sequence.items()
            elif iterable(sequence):
                ...
            else:
                assert sequence.is_Equal
                sequence = [sequence.args]
        else:
            if args[0].is_Equal:
                assert all(eq.is_Equal for eq in args)                
                sequence = [eq.args for eq in args]
            else:
                assert len(args) == 2, "subs accepts either 1 or 2 arguments"
                sequence = [args]

        from sympy import Symbol
        sequence = list(sequence)
        for i, s in enumerate(sequence):
            if isinstance(s[0], str):
                # when old is a string we prefer Symbol
                s = Symbol(s[0]), s[1]
            try:
                s = [sympify(_, strict=not isinstance(_, str)) for _ in s]
            except SympifyError:
                # if it can't be sympified, skip it
                sequence[i] = None
                continue
            # skip if there is no change
            sequence[i] = None if _aresame(*s) else tuple(s)
        sequence = list(filter(None, sequence))

        if unordered:
            sequence = dict(sequence)
            if not all(k.is_Atom for k in sequence):
                d = {}
                for o, n in sequence.items():
                    try:
                        ops = o.count_ops(), len(o.args)
                    except TypeError:
                        ops = (0, 0)
                    d.setdefault(ops, []).append((o, n))
                newseq = []
                for k in sorted(d.keys(), reverse=True):
                    newseq.extend(sorted([v[0] for v in d[k]], key=default_sort_key))
                sequence = [(k, sequence[k]) for k in newseq]
                del newseq, d
            else:
                sequence = sorted([(k, v) for (k, v) in sequence.items()], key=default_sort_key)

        if kwargs.pop('simultaneous', False):  # XXX should this be the default for dict subs?
            reps = {}
            rv = self
            kwargs['hack2'] = True
            from sympy import Dummy
            for old, new in sequence:

                d = Dummy(**new.type.dict)
                # using d*m so Subs will be used on dummy variables
                # in things like Derivative(f(x, y), x) in which x
                # is both free and bound
#                 rv = rv._subs(old, d * m, **kwargs)
                rv = rv._subs(old, d, **kwargs)
                if not isinstance(rv, Basic):
                    break
                reps[d] = new
#             reps[m] = S.One  # get rid of m
            return rv.xreplace(reps)
        else:
            rv = self
            for old, new in sequence:
                if old.is_Sliced:
                    rv = rv._subs_sliced(old, new, **kwargs)
                else:
                    rv = rv._subs(old, new, **kwargs)
                if not isinstance(rv, Basic):
                    break
            return rv
        
#    precondition: old is a Sliced object
#     @cacheit
    def _subs_sliced(self, old, new, **hints):
        hit = False
        args = [*self.args]
        for i, arg in enumerate(args):
            arg = arg._subs_sliced(old, new, **hints)
            if arg != args[i]:
                hit = True
                args[i] = arg
        if hit:
            return self.func(*args, **self.kwargs)
        return self
        
#     @cacheit
    def _subs(self, old, new, **hints):
        """Substitutes an expression old -> new.

        If self is not equal to old then _eval_subs is called.
        If _eval_subs doesn't want to make any special replacement
        then a None is received which indicates that the fallback
        should be applied wherein a search for replacements is made
        amongst the arguments of self.

        >>> from sympy import Add
        >>> from sympy.abc import x, y, z

        Examples
        ========

        Add's _eval_subs knows how to target x + y in the following
        so it makes the change:

        >>> (x + y + z).subs(x + y, 1)
        z + 1

        Add's _eval_subs doesn't need to know how to find x + y in
        the following:

        >>> Add._eval_subs(z*(x + y) + 3, x + y, 1) is None
        True

        The returned None will cause the fallback routine to traverse the args and
        pass the z*(x + y) arg to Mul where the change will take place and the
        substitution will succeed:

        >>> (z*(x + y) + 3).subs(x + y, 1)
        z + 3

        ** Developers Notes **

        An _eval_subs routine for a class should be written if:

            1) any arguments are not instances of Basic (e.g. bool, tuple);

            2) some arguments should not be targeted (as in integration
               variables);

            3) if there is something other than a literal replacement
               that should be attempted (as in Piecewise where the condition
               may be updated without doing a replacement).

        If it is overridden, here are some special cases that might arise:

            1) If it turns out that no special change was made and all
               the original sub-arguments should be checked for
               replacements then None should be returned.

            2) If it is necessary to do substitutions on a portion of
               the expression then _subs should be called. _subs will
               handle the case of any sub-expression being equal to old
               (which usually would not be the case) while its fallback
               will handle the recursion into the sub-arguments. For
               example, after Add's _eval_subs removes some matching terms
               it must process the remaining terms so it calls _subs
               on each of the un-matched terms and then adds them
               onto the terms previously obtained.

           3) If the initial expression should remain unchanged then
              the original expression should be returned. (Whenever an
              expression is returned, modified or not, no further
              substitution of old -> new is attempted.) Sum's _eval_subs
              routine uses this strategy when a substitution is attempted
              on any of its summation variables.
        """
        
        if old == new:
            return self

        if old.is_Sliced:
            this = self._subs_sliced(old, new, **hints)
            if this != self:
                return this
        
        def fallback(self, old, new):
            """
            Try to replace old with new in any of self's arguments.
            """
            hit = False
            args = [*self.args]
            for i, arg in enumerate(args):
                if not hasattr(arg, '_eval_subs'):
                    continue
                arg = arg._subs(old, new, **hints)
                if not _aresame(arg, args[i]):
                    hit = True
                    args[i] = arg
            if hit:
                rv = self.func(*args, **self.kwargs)
                hack2 = hints.get('hack2', False)
                if hack2 and self.is_Mul and not rv.is_Mul:  # 2-arg hack
                    coeff = S.One
                    nonnumber = []
                    for i in args:
                        if i.is_Number:
                            coeff *= i
                        else:
                            nonnumber.append(i)
                    nonnumber = self.func(*nonnumber)
                    if coeff is S.One:
                        return nonnumber
                    else:
                        return self.func(coeff, nonnumber, evaluate=False)
                return rv
            return self

        if _aresame(self, old) or self.dummy_eq(old):
            return new

        rv = self._eval_subs(old, new, **hints)
        if rv is None:
            rv = fallback(self, old, new)
        return rv

    def _eval_subs(self, old, new, **hints):
        """Override this stub if you want to do anything more than
        attempt a replacement of old with new in the arguments of self.

        See also
        ========

        _subs
        """
        ...

    def xreplace(self, rule):
        """
        Replace occurrences of objects within the expression.

        Parameters
        ==========

        rule : dict-like
            Expresses a replacement rule

        Returns
        =======

        xreplace : the result of the replacement

        Examples
        ========

        >>> from sympy import symbols, pi, exp
        >>> x, y, z = symbols('x y z')
        >>> (1 + x*y).xreplace({x: pi})
        pi*y + 1
        >>> (1 + x*y).xreplace({x: pi, y: 2})
        1 + 2*pi

        Replacements occur only if an entire node in the expression tree is
        matched:

        >>> (x*y + z).xreplace({x*y: pi})
        z + pi
        >>> (x*y*z).xreplace({x*y: pi})
        x*y*z
        >>> (2*x).xreplace({2*x: y, x: z})
        y
        >>> (2*2*x).xreplace({2*x: y, x: z})
        4*z
        >>> (x + y + 2).xreplace({x + y: 2})
        x + y + 2
        >>> (x + 2 + exp(x + 2)).xreplace({x + 2: y})
        x + exp(y) + 2

        xreplace doesn't differentiate between free and bound symbols. In the
        following, subs(x, y) would not change x since it is a bound symbol,
        but xreplace does:

        >>> from sympy import Integral
        >>> Integral(x, (x, 1, 2*x)).xreplace({x: y})
        Integral(y, (y, 1, 2*y))

        Trying to replace x with an expression raises an error:

        >>> Integral(x, (x, 1, 2*x)).xreplace({x: 2*y}) # doctest: +SKIP
        ValueError: Invalid limits given: ((2*y, 1, 4*y),)

        See Also
        ========
        replace: replacement capable of doing wildcard-like matching,
                 parsing of match, and conditional replacements
        subs: substitution of subexpressions as defined by the objects
              themselves.

        """
        value, _ = self._xreplace(rule)
        return value

    def _xreplace(self, rule):
        """
        Helper for xreplace. Tracks whether a replacement actually occurred.
        """
        if self in rule:
            return rule[self], True
        elif rule:
            args = []
            changed = False
            for a in self.args:
                _xreplace = getattr(a, '_xreplace', None)
                if _xreplace is not None:
                    a_xr = _xreplace(rule)
                    args.append(a_xr[0])
                    changed |= a_xr[1]
                else:
                    args.append(a)
            args = tuple(args)
            if changed:
                return self.func(*args), True
        return self, False

    @cacheit
    def has(self, *patterns):
        """
        Test whether any subexpression matches any of the patterns.

        Examples
        ========

        >>> from sympy import sin
        >>> from sympy.abc import x, y, z
        >>> (x**2 + sin(x*y)).has(z)
        False
        >>> (x**2 + sin(x*y)).has(x, y, z)
        True
        >>> x.has(x)
        True

        Note ``has`` is a structural algorithm with no knowledge of
        mathematics. Consider the following half-open interval:

        >>> from sympy.sets import Interval
        >>> i = Interval.Lopen(0, 5); i
        Interval.Lopen(0, 5)
        >>> i.args
        (0, 5, True, False)
        >>> i.has(4)  # there is no "4" in the arguments
        False
        >>> i.has(0)  # there *is* a "0" in the arguments
        True

        Instead, use ``contains`` to determine whether a number is in the
        interval or not:

        >>> i.contains(4)
        True
        >>> i.contains(0)
        False


        Note that ``expr.has(*patterns)`` is exactly equivalent to
        ``any(expr.has(p) for p in patterns)``. In particular, ``False`` is
        returned when the list of patterns is empty.

        >>> x.has()
        False

        """
        return any(self._has(pattern) for pattern in patterns)
    
    @cacheit
    def _has(self, pattern):
        """Helper for .has()"""
        if pattern.is_Tuple:
            return any(self._has(pattern) for pattern in pattern)
        from sympy.core.function import UndefinedFunction, Function
        if isinstance(pattern, UndefinedFunction):
            return any(f.func == pattern or f == pattern for f in self.atoms(Function, UndefinedFunction))

        pattern = sympify(pattern)
        if isinstance(pattern, BasicMeta):
            return any(isinstance(arg, pattern) for arg in preorder_traversal(self))

        has_match = getattr(pattern, 'has_match', None)
        if has_match is not None:
            if has_match(self):
                return True
        else:
            if self == pattern:
                return True

        return any(arg._has(pattern) for arg in self.args)

    def _has_matcher(self):
        """Helper for .has()"""
        return lambda other: self == other

    def replace(self, query, value, map=False, simultaneous=True, exact=None):
        """
        Replace matching subexpressions of ``self`` with ``value``.

        If ``map = True`` then also return the mapping {old: new} where ``old``
        was a sub-expression found with query and ``new`` is the replacement
        value for it. If the expression itself doesn't match the query, then
        the returned value will be ``self.xreplace(map)`` otherwise it should
        be ``self.subs(ordered(map.items()))``.

        Traverses an expression tree and performs replacement of matching
        subexpressions from the bottom to the top of the tree. The default
        approach is to do the replacement in a simultaneous fashion so
        changes made are targeted only once. If this is not desired or causes
        problems, ``simultaneous`` can be set to False.

        In addition, if an expression containing more than one Wild symbol
        is being used to match subexpressions and the ``exact`` flag is None
        it will be set to True so the match will only succeed if all non-zero
        values are received for each Wild that appears in the match pattern.
        Setting this to False accepts a match of 0; while setting it True
        accepts all matches that have a 0 in them. See example below for
        cautions.

        The list of possible combinations of queries and replacement values
        is listed below:

        Examples
        ========

        Initial setup

        >>> from sympy import log, sin, cos, tan, Wild, Mul, Add
        >>> from sympy.abc import x, y
        >>> f = log(sin(x)) + tan(sin(x**2))

        1.1. type -> type
            obj.replace(type, newtype)

            When object of type ``type`` is found, replace it with the
            result of passing its argument(s) to ``newtype``.

            >>> f.replace(sin, cos)
            log(cos(x)) + tan(cos(x**2))
            >>> sin(x).replace(sin, cos, map=True)
            (cos(x), {sin(x): cos(x)})
            >>> (x*y).replace(Mul, Add)
            x + y

        1.2. type -> func
            obj.replace(type, func)

            When object of type ``type`` is found, apply ``func`` to its
            argument(s). ``func`` must be written to handle the number
            of arguments of ``type``.

            >>> f.replace(sin, lambda arg: sin(2*arg))
            log(sin(2*x)) + tan(sin(2*x**2))
            >>> (x*y).replace(Mul, lambda *args: sin(2*Mul(*args)))
            sin(2*x*y)

        2.1. pattern -> expr
            obj.replace(pattern(wild), expr(wild))

            Replace subexpressions matching ``pattern`` with the expression
            written in terms of the Wild symbols in ``pattern``.

            >>> a, b = map(Wild, 'ab')
            >>> f.replace(sin(a), tan(a))
            log(tan(x)) + tan(tan(x**2))
            >>> f.replace(sin(a), tan(a/2))
            log(tan(x/2)) + tan(tan(x**2/2))
            >>> f.replace(sin(a), a)
            log(x) + tan(x**2)
            >>> (x*y).replace(a*x, a)
            y

            Matching is exact by default when more than one Wild symbol
            is used: matching fails unless the match gives non-zero
            values for all Wild symbols:

            >>> (2*x + y).replace(a*x + b, b - a)
            y - 2
            >>> (2*x).replace(a*x + b, b - a)
            2*x

            When set to False, the results may be non-intuitive:

            >>> (2*x).replace(a*x + b, b - a, exact=False)
            2/x

        2.2. pattern -> func
            obj.replace(pattern(wild), lambda wild: expr(wild))

            All behavior is the same as in 2.1 but now a function in terms of
            pattern variables is used rather than an expression:

            >>> f.replace(sin(a), lambda a: sin(2*a))
            log(sin(2*x)) + tan(sin(2*x**2))

        3.1. func -> func
            obj.replace(filter, func)

            Replace subexpression ``e`` with ``func(e)`` if ``filter(e)``
            is True.

            >>> g = 2*sin(x**3)
            >>> g.replace(lambda expr: expr.is_Number, lambda expr: expr**2)
            4*sin(x**9)

        The expression itself is also targeted by the query but is done in
        such a fashion that changes are not made twice.

            >>> e = x*(x*y + 1)
            >>> e.replace(lambda x: x.is_Mul, lambda x: 2*x)
            2*x*(2*x*y + 1)

        When matching a single symbol, `exact` will default to True, but
        this may or may not be the behavior that is desired:

        Here, we want `exact=False`:

        >>> from sympy import Function
        >>> f = Function('f')
        >>> e = f(1) + f(0)
        >>> q = f(a), lambda a: f(a + 1)
        >>> e.replace(*q, exact=False)
        f(1) + f(2)
        >>> e.replace(*q, exact=True)
        f(0) + f(2)

        But here, the nature of matching makes selecting
        the right setting tricky:

        >>> e = x**(1 + y)
        >>> (x**(1 + y)).replace(x**(1 + a), lambda a: x**-a, exact=False)
        x
        >>> (x**(1 + y)).replace(x**(1 + a), lambda a: x**-a, exact=True)
        x**(-x - y + 1)
        >>> (x**y).replace(x**(1 + a), lambda a: x**-a, exact=False)
        x
        >>> (x**y).replace(x**(1 + a), lambda a: x**-a, exact=True)
        x**(1 - y)

        It is probably better to use a different form of the query
        that describes the target expression more precisely:

        >>> (1 + x**(1 + y)).replace(
        ... lambda x: x.is_Pow and x.exp.is_Add and x.exp.args[0] == 1,
        ... lambda x: x.base**(1 - (x.exp - 1)))
        ...
        x**(1 - y) + 1

        See Also
        ========

        subs: substitution of subexpressions as defined by the objects
              themselves.
        xreplace: exact node replacement in expr tree; also capable of
                  using matching rules

        """
        from sympy.core.symbol import Dummy, Wild
        from sympy.simplify.simplify import bottom_up

        try:
            query = _sympify(query)
        except SympifyError:
            pass
        try:
            value = _sympify(value)
        except SympifyError:
            pass
        if isinstance(query, type):
            _query = lambda expr: isinstance(expr, query)

            if isinstance(value, type):
                _value = lambda expr, result: value(*expr.args)
            elif callable(value):
                _value = lambda expr, result: value(*expr.args)
            else:
                raise TypeError(
                    "given a type, replace() expects another "
                    "type or a callable")
        elif isinstance(query, Basic):
            _query = lambda expr: expr.match(query)
            if exact is None:
                exact = (len(query.atoms(Wild)) > 1)

            if isinstance(value, Basic):
                if exact:
                    _value = lambda expr, result: (value.subs(result)
                        if all(result.values()) else expr)
                else:
                    _value = lambda expr, result: value.subs(result)
            elif callable(value):
                # match dictionary keys get the trailing underscore stripped
                # from them and are then passed as keywords to the callable;
                # if ``exact`` is True, only accept match if there are no null
                # values amongst those matched.
                if exact:
                    _value = lambda expr, result: (value(**
                        {str(k)[:-1]: v for k, v in result.items()})
                        if all(val for val in result.values()) else expr)
                else:
                    _value = lambda expr, result: value(**
                        {str(k)[:-1]: v for k, v in result.items()})
            else:
                raise TypeError(
                    "given an expression, replace() expects "
                    "another expression or a callable")
        elif callable(query):
            _query = query

            if callable(value):
                _value = lambda expr, result: value(expr)
            else:
                raise TypeError(
                    "given a callable, replace() expects "
                    "another callable")
        else:
            raise TypeError(
                "first argument to replace() must be a "
                "type, an expression or a callable")

        mapping = {}  # changes that took place
        mask = []  # the dummies that were used as change placeholders

        def rec_replace(expr):
            result = _query(expr)
            if result or result == {}:
                new = _value(expr, result)
                if new is not None and new != expr:
                    mapping[expr] = new
                    if simultaneous:
                        # don't let this expression be changed during rebuilding
                        com = getattr(new, 'is_commutative', True)
                        if com is None:
                            com = True
                        d = Dummy(commutative=com)
                        mask.append((d, new))
                        expr = d
                    else:
                        expr = new
            return expr

        rv = bottom_up(self, rec_replace, atoms=True)

        # restore original expressions for Dummy symbols
        if simultaneous:
            mask = list(reversed(mask))
            for o, n in mask:
                r = {o: n}
                rv = rv.xreplace(r)

        if not map:
            return rv
        else:
            if simultaneous:
                # restore subexpressions in mapping
                for o, n in mask:
                    r = {o: n}
                    mapping = {k.xreplace(r): v.xreplace(r)
                        for k, v in mapping.items()}
            return rv, mapping

    def typeof(self, cls):
        if isinstance(cls, type):
            return isinstance(self, cls)
        if cls.is_Wanted:
            return self.typeof(cls.func)
        if isinstance(cls.kwargs, dict) and cls.kwargs:
            if isinstance(self, cls.func):
                return self.kwargs == cls.kwargs
            
            return self.typeof(cls.func)
        
        if isinstance(cls, Printable):
            return self == cls
        return self.typeof(cls.func)
        
    def of(self, cls, **kwargs):
        return self._extract(cls, **kwargs)
    
    def is_wanted(self):
        if self.is_Wanted:
            return True
        for arg in self.args:
            if isinstance(arg, type):
                continue
            if arg.is_wanted():
                return True
        return
    
    def find_path(self, cls, path, **kwargs):
        for i, arg in enumerate(self.args):
            if arg.typeof(cls):
                path.append(i)
                yield path
                path.pop()

        for i, arg in enumerate(self.args):
            path.append(i)
            yield from arg.find_path(cls, path, **kwargs)
            path.pop()

    def fetch_from_path(self, *path, **kwargs):
        struct = kwargs.get('struct')
        if struct is None:
            if kwargs.get('history'):
                history = []
                for index in path:
                    self = self.args[index] if isinstance(index, int) else getattr(self, index)
                    history.append(self)
                return history
            
            else:
                for index in path:
                    self = self.args[index]
                return self
            
        parent = []
        for index in path:
            parent.append(self)
            self = self.args[index]
        
        s = struct
        root_index = 0
        while True:
            if isinstance(s, type) or s.is_Wanted: 
                break
            
            root_index -= 1
            
            for i in range(-1, -len(s.args) - 1, -1): 
                arg = s.args[i]
                if isinstance(arg, type):
                    continue
                if arg.is_wanted():
                    break
            else:
                raise Exception('not wanted??')
                
            s = s.args[i]
        
        if root_index == 0:
            if not self.instanceof(struct):
                raise
        else:
            root = parent[root_index]
            if not root.isinstance(struct, *path[root_index:]):
                raise

            if isinstance(s.args, tuple):
                for arg in s.args:
                    if not isinstance(arg, type) and arg.is_wanted():
                        for path in self.finditer(arg, definition=True):
                            return path
        
        return self
    
    def isinstance(self, cls, t=None, *path):
        assert cls.is_Basic
        
        if not isinstance(self, cls.func):
            return False
        
        if t is None:
            if cls.is_wanted():
                if len(self.args) != len(cls.args):
                    return False
                
                for arg, struct in zip(self.args, cls.args):
                    if isinstance(struct, type):
                        if not isinstance(arg, struct):
                            return False
                        
                    elif struct.is_Number:
                        if arg != struct:    
                            return False
                        
                    else:
                        if not arg.isinstance(struct):
                            return False
                        
            else:
                if not self.of(cls):
                    return False
            return True
        
        for w, s in enumerate(cls.args):
            if s.is_Wanted or not isinstance(s, type) and (s.is_Basic or s.is_IndexedOperator) and s.is_wanted(): 
                if not self.args[t].instanceof(s):
                    return False
                break
        else:
            raise Exception('wanted not detected!')
        
        
        j = t - 1
#X[0], X[1], ..., X[t - 2], X[t - 1], X[t], X[t + 1], X[t + 2], ..., X[m - 1], m = len(X)
#                               j<---------------- start scanning from here
#C[0], C[1], ..., C[w - 2], C[w - 1], C[w], C[w + 1], C[w + 2], ..., C[n - 1], n = len(C)
#                               i<---------------- start scanning from here
#scan backward, starting from w - 1
        for i in range(w - 1, -1, -1):
            struct = cls.args[i]
            if j < 0:
                break

            if isinstance(struct, type):
                if isinstance(self.args[j], struct):
                    ...
                elif j and isinstance(self.args[j - 1], struct):
                    j -= 1
                else:
                    break
            elif struct.is_Number:
                if self.args[j] == struct:
                    ...
                elif j and self.args[j - 1] == struct:
                    j -= 1
                else:
                    break
            else:
                if not self.args[j].isinstance(struct, *path):
                    break
            
            j -= 1
            
        else:
            j = t + 1
#X[0], X[1], ..., X[t - 2], X[t - 1], X[t], X[t + 1], X[t + 2], ..., X[m - 1], m = len(X)
#start scanning from here --------------------->j
#C[0], C[1], ..., C[w - 2], C[w - 1], C[w], C[w + 1], C[w + 2], ..., C[n - 1], n = len(C)
#start scanning from here --------------------->i
#                 scan forward, starting from w + 1
            for i in range(w + 1, len(cls.args)):
                if j >= len(self.args):
                    break

                struct = cls.args[i]
                if isinstance(struct, type):
                    if isinstance(self.args[j], struct):
                        ...
                    elif j + 1 < len(self.args) and isinstance(self.args[j + 1], struct):
                        j += 1
                    else:
                        break
                elif struct.is_Number:
                    if self.args[j] == struct:
                        ...
                    elif j + 1 < len(self.args) and self.args[j + 1] == struct:
                        j += 1
                    else:
                        break
                else:
                    if not self.args[j].isinstance(struct, *path):
                        break
                    
                j += 1
                
            else:
                return True
                
        return False
        
    def instanceof(self, cls):
        if isinstance(cls, type):
            return isinstance(self, cls)
        
        if cls.is_Wanted: 
            if isinstance(cls.func, type):
                return isinstance(self, cls.func)
            
            cls = cls.func
                
        if not isinstance(self, cls.func):
            return False
        
        if cls.args:        
            j = 0
            i = 0
            while j < len(self.args):
                struct = cls.args[i]
                if self.args[j].instanceof(struct):
                    i += 1
                    if i == len(cls.args):
                        break
                j += 1
            else:
                return i == len(cls.args)
            
        return True
    
    def _extract(self, cls, indices=None):
        if isinstance(cls, type):
            if isinstance(self, cls):
                args = self.args
                if len(args) == 1:
                    return args[0]
                return args
            else:
                return
        
        if not isinstance(self, cls.func):
            return
        j = 0
        i = 0
        
        args = []
        while j < len(self.args):
            struct = cls._args[i]
            this = self.args[j]
            arg = this.of(struct)
            if arg is not None:
                if arg == ():
                    if not this.is_consistently_of(struct):
                        args.append(this)
                        if indices:
                            indices[i] = j
                else:
                    is_abstract = struct.is_abstract if isinstance(struct, type) else False
                    args.append(this if is_abstract else arg)
                    if indices:
                        indices[i] = j
                    
                i += 1
                if i == len(cls._args):
                    if args_rest := self.args[j + 1:]:
                        args.extend(args_rest)
                        if indices:
                            indices.append(slice(j + 1, None))
                    break
            else:
                args.append(this)
                if indices:
                    indices[i] = j
                
            j += 1
        else:
            if i == len(cls._args):
                return ()
            else:
                return
            
        args = tuple(args)
        while isinstance(args, tuple):
            if len(args) == 1:
                args = args[0]
            elif not args:
                return ()
            else:
                break
            
        return args
    
    @staticmethod
    def make_query(*query):
        if len(query) > 1 or isinstance(query[0], type): 
            if isinstance(query[-1], type):
                struct = (None,) * len(query)
            else:
                q_list = []
                struct = ()
                for q in query:
                    query, s = Basic.make_query(q)
                    q_list += query
                    struct += s 
                query = q_list
        else:
            struct, = query
            
            if not struct.is_Basic: 
                struct = struct.basic
                
            if not struct.is_wanted():
                from sympy.core.core import Wanted
                struct = Wanted(struct)
                    
            query = []
            s = struct
            while True:
                if isinstance(s, type) or s.is_Wanted:
                    query.append(s)
                    break
                
                if not s.is_Basic:
                    assert s.is_IndexedOperator
                    s = s.basic
                
                query.append(s.func)
                
                for i in range(-1, -len(s.args) - 1, -1):
                    arg = s.args[i]
                    if isinstance(arg, type):
                        continue
                    if arg.is_wanted():
                        break
                else:
                    raise Exception('not wanted??')
                s = s.args[i]
            struct = (None,) * (len(query) - 1) + (struct,)
            
        return query, struct
        
    def find(self, *query): 
        query, struct = Basic.make_query(*query)
            
        return self.yield_one([(q, []) for q in query],
                            foreach=Basic.find_path,
                            func=Basic.fetch_from_path,
                            fetch=self.fetch_from_path,
                            output=[],
                            struct=struct)
                    
    def finditer(self, *query, **kwargs):
        query, struct = Basic.make_query(*query)
        try:
            limits = [(q, []) for q in query]
            func = Basic.fetch_from_path
            output = []
            if kwargs:
                foreach = lambda self, *args: self.find_path(*args, **kwargs)
                fetch = lambda *path, **__: path
            else:
                foreach = Basic.find_path
                fetch = self.fetch_from_path
                
            yield from self.yield_all(limits, foreach, func, fetch, output, struct=struct)
        except GeneratorExit:
            ...
        
    def yield_one(self,
                limits,
                foreach=None,
                func=None,
                fetch=None,
                output=None,
                struct=None): 
            
        limit, *limits = limits
        struct, *structs = struct
        
        for _output in foreach(self, *limit):
            try: 
                if limits:
                    return func(self, *_output, struct=struct).yield_one(limits, foreach, func, fetch, output + _output, structs)
                else:
                    return fetch(*output, *_output, struct=struct)
            except Exception:
                continue
           
        if struct is not None and not limits:
            return fetch(*output, struct=struct)
             
        raise
                    
    def yield_all(self,
                limits,
                foreach=None,
                func=None,
                fetch=None,
                output=None,
                struct=None): 
            
        limit, *limits = limits
        struct, *structs = struct
        for _output in foreach(self, *limit):
            try: 
                if limits:
                    yield from func(self, *_output, struct=struct).yield_all(limits, foreach, func, fetch, output + _output, structs)
                else:
                    yield fetch(*output, *_output, struct=struct)
                    
            except GeneratorExit as e:
                raise e
            except: 
                continue
            
    def count(self, query):
        """Count the number of matching subexpressions. """
        query = _make_find_query(query)
        return sum(bool(query(sub)) for sub in preorder_traversal(self))

    def matches(self, expr, repl_dict={}, old=False):
        """
        Helper method for match() that looks for a match between Wild symbols
        in self and expressions in expr.

        Examples
        ========

        >>> from sympy import symbols, Wild, Basic
        >>> a, b, c = symbols('a b c')
        >>> x = Wild('x')
        >>> Basic(a + x, x).matches(Basic(a + b, c)) is None
        True
        >>> Basic(a + x, x).matches(Basic(a + b + c, b + c))
        {x_: b + c}
        """
        expr = sympify(expr)
        if not isinstance(expr, self.__class__):
            return None

        if self == expr:
            return repl_dict

        if len(self.args) != len(expr.args):
            return None

        d = repl_dict.copy()
        for arg, other_arg in zip(self.args, expr.args):
            if arg == other_arg:
                continue
            d = arg.xreplace(d).matches(other_arg, d, old=old)
            if d is None:
                return None
        return d

    def match(self, pattern, old=False):
        """
        Pattern matching.

        Wild symbols match all.

        Return ``None`` when expression (self) does not match
        with pattern. Otherwise return a dictionary such that::

          pattern.xreplace(self.match(pattern)) == self

        Examples
        ========

        >>> from sympy import Wild, Sum
        >>> from sympy.abc import x, y
        >>> p = Wild("p")
        >>> q = Wild("q")
        >>> r = Wild("r")
        >>> e = (x+y)**(x+y)
        >>> e.match(p**p)
        {p_: x + y}
        >>> e.match(p**q)
        {p_: x + y, q_: x + y}
        >>> e = (2*x)**2
        >>> e.match(p*q**r)
        {p_: 4, q_: x, r_: 2}
        >>> (p*q**r).xreplace(e.match(p*q**r))
        4*x**2

        Structurally bound symbols are ignored during matching:

        >>> Sum(x, (x, 1, 2)).match(Sum(y, (y, 1, p)))
        {p_: 2}

        But they can be identified if desired:

        >>> Sum(x, (x, 1, 2)).match(Sum(q, (q, 1, p)))
        {p_: 2, q_: x}

        The ``old`` flag will give the old-style pattern matching where
        expressions and patterns are essentially solved to give the
        match. Both of the following give None unless ``old=True``:

        >>> (x - 2).match(p - x, old=True)
        {p_: 2*x - 2}
        >>> (2/x).match(p*x, old=True)
        {p_: 2/x**2}

        """
        pattern = sympify(pattern)
        return pattern.matches(self, old=old)

    def count_ops(self, visual=None):
        """wrapper for count_ops that returns the operation count."""
        from sympy import count_ops
        return count_ops(self, visual)

    def doit(self, **hints):
        """Evaluate objects that are not evaluated by default like limits,
        integrals, sums and products. All objects of this kind will be
        evaluated recursively, unless some species were excluded via 'hints'
        or unless the 'deep' hint was set to 'False'.

        >>> from sympy import Integral
        >>> from sympy.abc import x

        >>> 2*Integral(x, x)
        2*Integral(x, x)

        >>> (2*Integral(x, x)).doit()
        x**2

        >>> (2*Integral(x, x)).doit(deep=False)
        2*Integral(x, x)

        """
        if hints.get('deep', True):
            args = [term.doit(**hints) if isinstance(term, Basic) else term for term in self.args]
            return self.func(*args, **self.kwargs)
        else:
            return self

    def simplify(self, deep=False, **kwargs):
        if deep:
            hit = False
            args = []
            for arg in self.args: 
                _arg = arg.simplify(deep=True, **kwargs)
                if _arg != arg:
                    hit = True
                args.append(_arg)
            if hit:
                return self.func(*args).simplify()

        return self

    def refine(self, assumption=True):
        """See the refine function in sympy.assumptions"""
        from sympy.assumptions import refine
        return refine(self, assumption)

    def _eval_rewrite(self, pattern, rule, **hints):
        if self.is_Atom:
            if hasattr(self, rule):
                return getattr(self, rule)()
            return self

        if hints.get('deep', True):
            args = [a._eval_rewrite(pattern, rule, **hints)
                        if isinstance(a, Basic) else a
                        for a in self.args]
        else:
            args = self.args

        if pattern is None or isinstance(self, pattern):
            if hasattr(self, rule):
                rewritten = getattr(self, rule)(*args, **hints)
                if rewritten is not None:
                    return rewritten

        return self.func(*args) if hints.get('evaluate', True) else self

    def _accept_eval_derivative(self, s):
        # This method needs to be overridden by array-like objects
        return s._visit_eval_derivative_scalar(self)

    def _visit_eval_derivative_scalar(self, base):
        # Base is a scalar
        # Types are (base: scalar, self: scalar)
        return base._eval_derivative(self)

    def _visit_eval_derivative_array(self, base):
        # Types are (base: array/matrix, self: scalar)
        # Base is some kind of array/matrix,
        # it should have `.applyfunc(lambda x: x.diff(self)` implemented:
        return base._eval_derivative_array(self)

    def _eval_derivative_n_times(self, s, n):
        # This is the default evaluator for derivatives (as called by `diff`
        # and `Derivative`), it will attempt a loop to derive the expression
        # `n` times by calling the corresponding `_eval_derivative` method,
        # while leaving the derivative unevaluated if `n` is symbolic.  This
        # method should be overridden if the object has a closed form for its
        # symbolic n-th derivative.
        from sympy import Integer
        if isinstance(n, (int, Integer)):
            obj = self
            for i in range(n):
                obj2 = obj._accept_eval_derivative(s)
                if obj == obj2 or obj2 is None:
                    break
                obj = obj2
            return obj2
        else:
            return None

    def rewrite(self, *args, **hints):
        """ Rewrite functions in terms of other functions.

        Rewrites expression containing applications of functions
        of one kind in terms of functions of different kind. For
        example you can rewrite trigonometric functions as complex
        exponentials or combinatorial functions as gamma function.

        As a pattern this function accepts a list of functions to
        to rewrite (instances of DefinedFunction class). As rule
        you can use string or a destination function instance (in
        this case rewrite() will use the str() function).

        There is also the possibility to pass hints on how to rewrite
        the given expressions. For now there is only one such hint
        defined called 'deep'. When 'deep' is set to False it will
        forbid functions to rewrite their contents.

        Examples
        ========

        >>> from sympy import sin, exp
        >>> from sympy.abc import x

        Unspecified pattern:

        >>> sin(x).rewrite(exp)
        -I*(exp(I*x) - exp(-I*x))/2

        Pattern as a single function:

        >>> sin(x).rewrite(sin, exp)
        -I*(exp(I*x) - exp(-I*x))/2

        Pattern as a list of functions:

        >>> sin(x).rewrite([sin, ], exp)
        -I*(exp(I*x) - exp(-I*x))/2

        """
        if not args:
            return self
        else:
            pattern = args[:-1]
            if isinstance(args[-1], str):
                rule = '_eval_rewrite_as_' + args[-1]
            else:
                try:
                    rule = '_eval_rewrite_as_' + args[-1].__name__
                except:
                    rule = '_eval_rewrite_as_' + args[-1].__class__.__name__

            if not pattern:
                return self._eval_rewrite(None, rule, **hints)
            else:
                if iterable(pattern[0]):
                    pattern = pattern[0]

                pattern = [p for p in pattern if self.has(p)]

                if pattern:
                    return self._eval_rewrite(tuple(pattern), rule, **hints)
                else:
                    return self

    _constructor_postprocessor_mapping = {}

    @classmethod
    def _exec_constructor_postprocessors(cls, obj):

        # WARNING: This API is experimental.

        # This is an experimental API that introduces constructor
        # postprosessors for SymPy Core elements. If an argument of a SymPy
        # expression has a `_constructor_postprocessor_mapping` attribute, it will
        # be interpreted as a dictionary containing lists of postprocessing
        # functions for matching expression node names.

        clsname = obj.__class__.__name__
        postprocessors = defaultdict(list)
        for i in obj.args:
            try:
                postprocessor_mappings = (
                    Basic._constructor_postprocessor_mapping[cls].items()
                    for cls in type(i).mro()
                    if cls in Basic._constructor_postprocessor_mapping
                )
                for k, v in chain.from_iterable(postprocessor_mappings):
                    postprocessors[k].extend([j for j in v if j not in postprocessors[k]])
            except TypeError:
                pass

        for f in postprocessors.get(clsname, []):
            obj = f(obj)

        return obj

    @property
    def latex(self):
        from sympy.printing.latex import latex
        return latex(self)

    @property
    def lean(self):
        from sympy.printing.lean import lean
        return lean(self)

    @property
    def python(self):
        random_symbols = set()
        definition = self.python_definition(set(), random_symbols)
        defun = [defun for var, defun in definition]
        from sympy.printing.str import StrPrinter
        p = StrPrinter(dict(order=None))
        p._context['random_symbols'] = {v.var for v in random_symbols}
        defun.append(p._print(self))
        return '\n'.join(defun)
    
    def python_definition(self, free_symbols, random_symbols):
        from sympy import Symbol
        definition = []
        for arg in self.args:
            Symbol.definition_append(definition, arg.python_definition(free_symbols, random_symbols))
        return definition
     
    def _eval_domain_defined(self, x, **_):
        if x.dtype.is_set:
            return x.universalSet
        return x.domain
    
    @property
    def type(self):
        return self.dtype[self.shape]
    
    @staticmethod
    def yield_vars(sym):
        if isinstance(sym, set):
            for sym in sym:
                yield from Basic.yield_vars(sym)
                
        elif sym.is_Symbol:
            yield sym.name
            
        else:
            for sym in sym.free_symbols - {sym}:
                yield from Basic.yield_vars(sym)
                
    def generate_var(self, excludes=None, var=None, **kwargs):
        if excludes is None:
            excludes = set()
        elif not isinstance(excludes, set):
            excludes = {excludes}
            
        excludes = {*Basic.yield_vars(excludes | self.free_symbols)}
        
        from sympy import Symbol
        if var is not None:
            if isinstance(var, set):
                for v in var:
                    if isinstance(v, str):
                        if v not in excludes:
                            return Symbol(v, **kwargs)
                    elif v.name not in excludes:
                        return v
                
            else:
                if isinstance(var, str):
                    var = Symbol(var, **kwargs)
                else:
                    assert var.is_symbol
                        
                if var.name not in excludes:
                    return var
                    
        if 'definition' in kwargs:
            definition = kwargs['definition']
            shape = definition.shape
            if shape:
                kwargs['shape'] = definition.shape
            elif definition.is_set:
                kwargs['etype'] = definition.etype
            elif definition.is_integer:
                kwargs['integer'] = True
            
        if 'shape' in kwargs: 
            if len(kwargs['shape']) > 1:
                symbols = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
            else:
                symbols = 'abcdefgopqrstuvwxyzhijklmn'
        elif 'etype' in kwargs:
            symbols = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'            
        elif 'integer' in kwargs:
            symbols = 'ijkhtdlmnabcefgopqrsuvwxyz'
        else:
            symbols = 'xyzabcdefghijklmnopqrstuvw'
        
        for name in symbols:
            if name not in excludes: 
                return Symbol(name, **kwargs)
        raise Exception("run out of symbols")

    # performing other in self
    def contains_with_subset(self, other):
        other = sympify(other)
        if other.is_EmptySet:
            return True
        if self.is_EmptySet:
            return
        
        if self.is_UniversalSet:
            if other.etype in self.etype:
                return True
            
        if other.is_UniversalSet:
            if self.is_FiniteSet:
                return False
            
        if other.type in self.type or self.type in other.type:
            return other.is_subset(self)

    def _contains(self, other):
        ...
        
    def contains(self, other):
        other = sympify(other, strict=True)
        ret = sympify(self._contains(other))
        if ret is not None and ret.is_BooleanAtom:
            return ret
            
        domain_assumed = other.domain_assumed
        if domain_assumed:
            intersect = domain_assumed & self
            if not intersect:
                return S.false
            if intersect == domain_assumed:
                return S.true

    def infimum(self):
        return self
    
    def supremum(self):
        return self
        
    def handle_finite_sets(self, _):
        ...
        
    @property
    def domain_assumed(self):
        ...
    
    def _ask(self, fact):
        """
        Find the truth value for a property of an object.
    
        This function is called when a request is made to see what a fact
        value is.
    
        For this we use several techniques:
    
        First, the fact-evaluation function is tried, if it exists (for
        example _eval_is_integer). Then we try related facts. For example
    
            rational   -->   integer
    
        another example is joined rule:
    
            integer & !odd  --> even
    
        so in the latter case if we are looking at what 'even' value is,
        'integer' and 'odd' facts will be asked.
    
        In all cases, when we settle on some fact value, its implications are
        deduced, and the result is cached in ._assumptions.
        """
        assumptions = self._assumptions
        
        def sufficient_conditions(b):
            for sufficient_fact, truth in _assume_rules.sufficient_conditions[(fact, b)]:
                if assumptions.get(sufficient_fact) == truth:
                    return b
            
        from sympy.core.assumptions import _assume_rules
        a = sufficient_conditions(True)
        if a is None:
            a = sufficient_conditions(False)
        
        if a is None:
            evaluate = self._prop_handler.get(fact)
            if evaluate is not None:
                a = evaluate(self)
        assumptions[fact] = a
        return a
    
    def _eval_is_integer(self):
        finite = self.is_finite
        if finite:
            return self.is_extended_integer
        if finite == False:
            return False

    def _eval_is_rational(self):
        finite = self.is_finite
        if finite:
            return self.is_extended_rational
        if finite == False:
            return False

    def _eval_is_real(self):
        finite = self.is_finite
        if finite:
            return self.is_extended_real
        if finite == False:
            return False

    def _eval_is_complex(self):
        finite = self.is_finite
        if finite:
            return self.is_extended_complex
        if finite == False:
            return False
    
    def _eval_is_extended_nonpositive(self):
        extended_positive = self.is_extended_positive
        if extended_positive:
            return False
        if extended_positive == False:
            return self.is_extended_real

    def _eval_is_extended_nonnegative(self):
        extended_negative = self.is_extended_negative
        if extended_negative:
            return False
        if extended_negative == False:
            return self.is_extended_real
    
    def _eval_is_infinite(self):
        from sympy.core.logic import fuzzy_not
        return fuzzy_not(self.is_finite)
        
    def _eval_is_infiniteset(self):
        from sympy.core.logic import fuzzy_not
        return fuzzy_not(self.is_finiteset)
    
    def _eval_is_transcendental(self):
        algebraic = self.is_algebraic
        if algebraic:
            return False
        if algebraic == False:
            if self.is_complex:
                return self.is_finite
            return self.is_complex
        
    def _eval_is_irrational(self):
        rational = self.is_rational
        if rational:
            return False
        if rational == False:
            return self.is_real

    def _eval_is_noninteger(self):
        integer = self.is_integer
        if integer:
            return False
        if integer == False:
            return self.is_extended_real
    
    def _eval_is_invertible(self):
        singular = self.is_singular
        if singular:
            return False
        if singular == False:
            return True

    def _eval_is_nonzero(self):
        if self.shape:
            return
            
        zero = self.is_zero
        if zero:
            return False
        if zero == False:
            return self.is_complex

    def _eval_shape(self):
        if 'shape' in self._assumptions:
            return self._assumptions['shape']
        return ()
    
    @property
    def shape(self):
        return self._eval_shape()
    
    @property
    def this(self):
        from sympy.logic.invoker import Identity
        return Identity(self)
      
    def domain_definition(self, **_):
        return S.true
      
    @classmethod
    def simplify_ForAll(cls, self, *args):
        ...

    @classmethod
    def simplify_Unequal(cls, self, lhs, rhs):
        ...

    @classmethod
    def simplify_Element(cls, self, lhs, rhs):
        ...

    @classmethod
    def simplify_NotElement(cls, self, lhs, rhs):
        ...
        
    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        ...
        
    @classmethod
    def simplify_Relational(cls, self, lhs, rhs):
        ...
        
    def domain_defined(self, x, **kwargs):
        if x in self.free_symbols:
            return self._eval_domain_defined(x, **kwargs)

        domain = Basic._eval_domain_defined(self, x)
        for v in self.variables:
            if v._has(x):
                domain &= v._eval_domain_defined(x, **kwargs)
        return domain

    def domain_defined_for_limits(self, limits):
        domain_defined = {}
        for v, *_ in limits:
            domain_defined[v] = self.domain_defined(v)        
        return domain_defined
    
    @property
    def emptySet(self):
        from sympy.sets.sets import EmptySet
        return EmptySet(etype=self.type)
    
    @property
    def universalSet(self):
        from sympy.sets.sets import UniversalSet
        return UniversalSet(etype=self.type)
    
    def _eval_Subset_reversed(self, lhs):
        ...
    
    def _eval_Subset(self, rhs):
        ...

    def apply(self, axiom, *args, **kwargs):
        try:
            eq = axiom.apply(self, *args, **kwargs)
        except Exception as e:
            import traceback
            traceback.print_exc()
            print(e)
            return
        assert eq.is_Equal
        assert eq.lhs is self
        return eq.rhs
    
    def floor(self):
        from sympy import Floor
        return Floor(self)

    def ceil(self):
        from sympy import Ceil
        return Ceil(self)
    
    def inference_status(self, child):
        return False
    
    def _eval_Card(self):
        ...
      
      
    def yield_substituent(self, x, *limits):
        for i in x.free_symbols:
            if i.shape:
                continue
            if i.domain_assumed:
                continue
            domain = self.domain_defined(i)
            for var, *ab in limits:
                if i == var:
                    if len(ab) == 2:
                        domain &= i.range(*ab)
                    elif len(ab) == 1:
                        s, = ab
                        domain &= s
                    break
                
            yield x._subs(i, i.copy(domain=domain))
        
    def bound_check(self, x, *limits, lower=None, upper=None):

        if lower is not None:
            if x >= lower:
                return True
            if not any(x >= lower for x in self.yield_substituent(x, *limits)):
                return False
        
        if upper is not None:
            if x <= upper:
                return True
            
            if not any(x <= upper for x in self.yield_substituent(x, *limits)):
                return False

        return True
      
    def adjust_domain(self, x, *cond):
        return self
      
    def max_len_shape(self):
        return max(len(arg.shape) for arg in self.args)    

    is_given = True

    @cacheit
    def variables_with_limits(self, excludes=None):
        indices = []
        if excludes is None:
            excludes = set()
        for _ in self.shape:
            i = self.generate_var(excludes=excludes, integer=True)
            indices.append(i)
            excludes.add(i)
        
        limits = []
        for size, i in zip(self.shape, indices):
            limits.append((i, 0, size))

        limits.reverse()
        return indices, limits
    
    @cacheit
    def unsqueeze(self, axis, size):
        indices, limits = self.variables_with_limits()
        from sympy.core.symbol import Symbol
        i = Symbol('', integer=True)
        
        if axis < 0:
            axis += len(limits) + 1
            
        index = len(limits) - axis
        from sympy.concrete.expr_with_limits import Stack
        tensor = Stack(self[tuple(indices)], *limits[:index], (i, 0, size), *limits[index:]).simplify()
        try:
            S[self], S[axis], S[size] = tensor.of_unsqueeze()
        except Exception as e:
            print(e)
            S[self], S[axis], S[size] = tensor.of_unsqueeze()
        return tensor
        
    #precondition: self is a boolean matrix
    def where(self, lhs, rhs):
        limits = self._limits
        indices = self._variables
        
        from sympy.concrete.expr_with_limits import Stack
        from sympy.functions.elementary.piecewise import Piecewise
        
        return Stack(
            Piecewise(
                (lhs[indices], self[indices]),
                (rhs[indices], True)), 
            *limits)
        
    def gather(self, indices, axis=1):
        #precondition: indices must be nonnegative in case of index error
        args, limits = indices.variables_with_limits({*self.free_symbols})
        args = tuple(args)
        from sympy.concrete.expr_with_limits import Stack
        return Stack(self[(*args[:axis], indices[args], *args[axis + 1:])], *limits)
    
    def is_default_slice(self, index, length=1):
        if isinstance(index, slice):
            if index.step is None or index.step == 1:
                if index.start is None or index.start == 0:
                    if index.stop is None or index.stop == self.shape[length - 1]:
                        return True
                    
    def last_is_default_slice(self, indices):
        return self.is_default_slice(indices[-1], len(indices))
    
    def simplify_indices(self, indices):
        from sympy.core.containers import Tuple
        shape = self.shape

        if isinstance(indices, tuple):
            while True:
                if not indices:
                    return
                
                if self.last_is_default_slice(indices):
                    indices = indices[:-1]
                else:
                    break

            
            arr = {}
            i = 0
            for index in indices:
                if isinstance(index, slice):
                    arr[i] = Tuple.from_slice(index, size=shape[i])
                elif index is ...:
                    diff = len(shape) - len(indices) + 1
                    if not diff:
                        indices = indices[:i] + indices[i + 1:]
                        continue

                    index = Tuple.from_slice(slice(None), size=shape[i])
                    if diff > 1:
                        indices = indices[:i] + (index,) * diff + indices[i + 1:]
                        i += diff
                        continue
                    
                    arr[i] = index
                i += 1

            if arr:
                indices = [*indices]
                for k, v in arr.items():
                    indices[k] = v
                indices = tuple(indices)

            if len(indices) == 1:
                indices, = indices

        elif isinstance(indices, slice):
            if self.is_default_slice(indices):
                return
            
            indices = Tuple.from_slice(indices, size=shape[0])
        
        elif isinstance(indices, list):
            while True:
                if not indices:
                    return

                if self.last_is_default_slice(indices):
                    indices.pop()
                else:
                    break
            
            i = 0
            while i < len(indices):
                index = indices[i]
                if isinstance(index, slice):
                    indices[i] = Tuple.from_slice(index, size=shape[i])
                elif index is ...:
                    diff = len(shape) - len(indices) + 1
                    if not diff:
                        del indices[i]
                        continue

                    index = Tuple.from_slice(slice(None), size=shape[i])
                    if diff > 1:
                        indices[index: index + 1] = [index] * diff
                        i += diff
                        continue
                    indices[i] = index
                i += 1

            if len(indices) == 1:
                indices, = indices
            else:
                indices = tuple(indices)

        return indices

    def flip(self, axis=-1):
        indices, limits = self.variables_with_limits()
        size = self.shape[axis]
        i = indices[axis]
        i = size - 1 - i
        indices[axis] = i
        from sympy.concrete.expr_with_limits import Stack
        return Stack(self[tuple(indices)], *limits)
    
    def expand_indices(self, limits, **kwargs):
        return self
    
    @staticmethod
    def simplify_Lamda(self, squeeze=False):
        return self
    
    def precompile(self, *sym):
        indices = []
        vars = []  
        for i, v in enumerate(sym):
            if self._has(v):
                indices.append(i)
                vars.append(v)
                
        if vars:
            return self.compile(*vars), indices
        return self, None
    
    @property
    def variables(self):
        return []

    def conditionally_contains(self, x):
        return x in self

    def limits_in_context(self, *args):
        return []

    def is_consistently_of(self, struct):
        return True

    def _sympystr(self, p):
        return self.__class__.__name__ + "(%s)" % ", ".join(p._print(o) for o in self.args)

    def _lean(self, p):
        return self.__class__.__name__ + "(%s)" % ", ".join(p._print(o) for o in self.args)

    def _latex(self, p, exp=None):
        tex = p._deal_with_super_sub(self.__class__.__name__) + r"\left(%s\right)" % ", ".join(p._print(o) for o in self.args)
        if exp:
            tex = r'%s^{%s}' % (tex, p._print(exp))
        return tex

    def normalize_reduced_axis(self, axis):
        if isinstance(axis, tuple):
            axis = [*axis]
            for i, a in enumerate(axis):
                if a < 0:
                    a += len(self.shape)
                    hit = True
                    axis[i] = a

            axis.sort()
            return tuple(axis)
        else:
            if axis < 0:
                axis += len(self.shape)
            return axis

    @property
    def default_axis(self):
        return len(self.arg.shape) - 1


class Atom(Basic):
    """
    A parent class for atomic things. An atom is an expression with no subexpressions.

    Examples
    ========

    Symbol, Number, Rational, Integer, ...
    But not: Add, Mul, Pow, ...
    """

    __slots__ = ()

    def matches(self, expr, repl_dict={}, old=False):
        if self == expr:
            return repl_dict

    def xreplace(self, rule, hack2=False):
        return rule.get(self, self)

    def doit(self, **hints):
        return self

    @classmethod
    def class_key(cls):
        return 2, 0, cls.__name__

    @cacheit
    def sort_key(self, order=None):
        return self.class_key(), (0, (), (str(self),)), S.One.sort_key(), S.One

    def _eval_simplify(self, **kwargs):
        return self

    @property
    def _sorted_args(self):
        # this is here as a safeguard against accidentally using _sorted_args
        # on Atoms -- they cannot be rebuilt as atom.func(*atom._sorted_args)
        # since there are no args. So the calling routine should be checking
        # to see that this property is not called for Atoms.
        raise AttributeError('Atoms have no args. It might be necessary'
        ' to make a check for Atoms in the calling code.')


def _aresame(a, b):
    """Return True if a and b are structurally the same, else False.

    Examples
    ========

    In SymPy (as in Python) two numbers compare the same if they
    have the same underlying base-2 representation even though
    they may not be the same type:

    >>> from sympy import S
    >>> 2.0 == S(2)
    True
    >>> 0.5 == S.Half
    True

    This routine was written to provide a query for such cases that
    would give false when the types do not match:

    >>> from sympy.core.basic import _aresame
    >>> _aresame(S(2.0), S(2))
    False

    """
    from .numbers import Number
    from .function import AppliedUndef, UndefinedFunction as UndefFunc
    if isinstance(a, Number) and isinstance(b, Number):
        return a == b and a.__class__ == b.__class__
    for i, j in zip_longest(preorder_traversal(a), preorder_traversal(b)):
        if i != j or type(i) != type(j):
            if ((isinstance(i, UndefFunc) and isinstance(j, UndefFunc)) or
                (isinstance(i, AppliedUndef) and isinstance(j, AppliedUndef))):
                if i.class_key() != j.class_key():
                    return False
            else:
                return False
    return True


def _ne(a, b):
    # use this as a second test after `a != b` if you want to make
    # sure that things are truly equal, e.g.
    # a, b = 0.5, S.Half
    # a !=b or _ne(a, b) -> True
    from .numbers import Number
    # 0.5 == S.Half
    if isinstance(a, Number) and isinstance(b, Number):
        return a.__class__ != b.__class__


def _atomic(e, recursive=False):
    """Return atom-like quantities as far as substitution is
    concerned: Derivatives, Functions and Symbols. Don't
    return any 'atoms' that are inside such quantities unless
    they also appear outside, too, unless `recursive` is True.

    Examples
    ========

    >>> from sympy import Derivative, Function, cos
    >>> from sympy.abc import x, y
    >>> from sympy.core.basic import _atomic
    >>> f = Function('f')
    >>> _atomic(x + y)
    {x, y}
    >>> _atomic(x + f(y))
    {x, f(y)}
    >>> _atomic(Derivative(f(x), x) + cos(x) + y)
    {y, cos(x), Derivative(f(x), x)}

    """
    from sympy import Derivative, Function, Symbol
    pot = preorder_traversal(e)
    seen = set()
    if isinstance(e, Basic):
        free = getattr(e, "free_symbols", None)
        if free is None:
            return {e}
    else:
        return set()
    atoms = set()
    for p in pot:
        if p in seen:
            pot.skip()
            continue
        seen.add(p)
        if isinstance(p, Symbol) and p in free:
            atoms.add(p)
        elif isinstance(p, (Derivative, Function)):
            if not recursive:
                pot.skip()
            atoms.add(p)
    return atoms


class preorder_traversal:
    """
    Do a pre-order traversal of a tree.

    This iterator recursively yields nodes that it has visited in a pre-order
    fashion. That is, it yields the current node then descends through the
    tree breadth-first to yield all of a node's children's pre-order
    traversal.


    For an expression, the order of the traversal depends on the order of
    .args, which in many cases can be arbitrary.

    Parameters
    ==========
    node : sympy expression
        The expression to traverse.
    keys : (default None) sort key(s)
        The key(s) used to sort args of Basic objects. When None, args of Basic
        objects are processed in arbitrary order. If key is defined, it will
        be passed along to ordered() as the only key(s) to use to sort the
        arguments; if ``key`` is simply True then the default keys of ordered
        will be used.

    Yields
    ======
    subtree : sympy expression
        All of the subtrees in the tree.

    Examples
    ========

    >>> from sympy import symbols
    >>> from sympy.core.basic import preorder_traversal
    >>> x, y, z = symbols('x y z')

    The nodes are returned in the order that they are encountered unless key
    is given; simply passing key=True will guarantee that the traversal is
    unique.

    >>> list(preorder_traversal((x + y)*z, keys=None)) # doctest: +SKIP
    [z*(x + y), z, x + y, y, x]
    >>> list(preorder_traversal((x + y)*z, keys=True))
    [z*(x + y), z, x + y, x, y]

    """

    def __init__(self, node, keys=None):
        self._skip_flag = False
        self._pt = self._preorder_traversal(node, keys)

    def _preorder_traversal(self, node, keys):
        yield node
        if self._skip_flag:
            self._skip_flag = False
            return
        if isinstance(node, Basic):
            if not keys and hasattr(node, '_argset'):
                # LatticeOp keeps args as a set. We should use this if we
                # don't care about the order, to prevent unnecessary sorting.
                args = node._argset
            else:
                args = node.args
            if keys:
                if keys != True:
                    args = ordered(args, keys, default=False)
                else:
                    args = ordered(args)
            for arg in args:
                yield from self._preorder_traversal(arg, keys)

    def skip(self):
        """
        Skip yielding current node's (last yielded node's) subtrees.

        Examples
        ========

        >>> from sympy.core import symbols
        >>> from sympy.core.basic import preorder_traversal
        >>> x, y, z = symbols('x y z')
        >>> pt = preorder_traversal((x+y*z)*z)
        >>> for i in pt:
        ...     print(i)
        ...     if i == x+y*z:
        ...             pt.skip()
        z*(x + y*z)
        z
        x + y*z
        """
        self._skip_flag = True

    def __next__(self):
        return next(self._pt)

    def __iter__(self):
        return self


def _make_find_query(query):
    """Convert the argument of Basic.find() into a callable"""
    try:
        query = _sympify(query)
    except SympifyError:
        pass
    if isinstance(query, type):
        return lambda expr: isinstance(expr, query)
    elif isinstance(query, Basic):
        return lambda expr: expr.match(query) is not None
    return query


# Delayed to avoid cyclic import
from .singleton import S
