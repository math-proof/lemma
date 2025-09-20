"""
This module contains the machinery handling assumptions.

All symbolic objects have assumption attributes that can be accessed via
.is_<assumption name> attribute.

Assumptions determine certain properties of symbolic objects and can
have 3 possible values: True, False, None.  True is returned if the
object has the property and False is returned if it doesn't or can't
(i.e. doesn't make sense):

    >>> from sympy import I
    >>> I.is_algebraic
    True
    >>> I.is_real
    False
    >>> I.is_prime
    False

When the property cannot be determined (or when a method is not
implemented) None will be returned, e.g. a generic symbol, x, may or
may not be positive so a value of None is returned for x.is_positive.

By default, all symbolic values are in the largest set in the given context
without specifying the property. For example, a symbol that has a property
being integer, is also real, complex, etc.

Here follows a list of possible assumption names:

.. glossary::

    complex
        object can have only values from the set
        of complex numbers.

    imaginary
        object value is a number that can be written as a real
        number multiplied by the imaginary unit ``I``.  See
        [3]_.  Please note that ``0`` is not considered to be an
        imaginary number, see
        `issue #7649 <https://github.com/sympy/sympy/issues/7649>`_.

    real
        object can have only values from the set
        of real numbers.

    integer
        object can have only values from the set
        of integers.

    odd
    even
        object can have only values from the set of
        odd (even) integers [2]_.

    prime
        object is a natural number greater than ``1`` that has
        no positive divisors other than ``1`` and itself.  See [6]_.

    composite
        object is a positive integer that has at least one positive
        divisor other than ``1`` or the number itself.  See [4]_.

    zero
        object has the value of ``0``.

    nonzero
        object is a complex number that is not zero.

    rational
        object can have only values from the set
        of rationals.

    algebraic
        object can have only values from the set
        of algebraic numbers [11]_.

    transcendental
        object can have only values from the set
        of transcendental numbers [10]_.

    irrational
        object value cannot be represented exactly by Rational, see [5]_.

    finite
    infinite
        object absolute value is bounded (arbitrarily large).
        See [7]_, [8]_, [9]_.

    negative
    nonnegative
        object can have only negative (nonnegative)
        values [1]_.

    positive
    nonpositive
        object can have only positive (only
        nonpositive) values.

    hermitian
    antihermitian
        object belongs to the field of hermitian
        (antihermitian) operators.

Examples
========

    >>> from sympy import Symbol
    >>> x = Symbol('x', real=True); x
    x
    >>> x.is_real
    True
    >>> x.is_complex
    True

See Also
========

.. seealso::

    :py:class:`sympy.core.numbers.ImaginaryUnit`
    :py:class:`sympy.core.numbers.Zero`
    :py:class:`sympy.core.numbers.One`

Notes
=====

The fully-resolved assumptions for any SymPy expression
can be obtained as follows:

    >>> from sympy.core.assumptions import assumptions
    >>> x = Symbol('x',positive=True)
    >>> assumptions(x + I)
    {'commutative': True, 'complex': True, 'composite': False, 'even':
    False, 'extended_negative': False, 'extended_nonnegative': False,
    'extended_nonpositive': False, 'extended_nonzero': False,
    'extended_positive': False, 'extended_real': False, 'finite': True,
    'imaginary': False, 'infinite': False, 'integer': False, 'irrational':
    False, 'negative': False, 'noninteger': False, 'nonnegative': False,
    'nonpositive': False, 'nonzero': False, 'odd': False, 'positive':
    False, 'prime': False, 'rational': False, 'real': False, 'zero':
    False}

Developers Notes
================

The current (and possibly incomplete) values are stored
in the ``obj._assumptions dictionary``; queries to getter methods
(with property decorators) or attributes of objects/classes
will return values and update the dictionary.

    >>> eq = x**2 + I
    >>> eq._assumptions
    {}
    >>> eq.is_finite
    True
    >>> eq._assumptions
    {'finite': True, 'infinite': False}

For a Symbol, there are two locations for assumptions that may
be of interest. The ``assumptions0`` attribute gives the full set of
assumptions derived from a given set of initial assumptions. The
latter assumptions are stored as ``Symbol._assumptions.generator``

    >>> Symbol('x', prime=True, even=True)._assumptions.generator
    {'even': True, 'prime': True}

The ``generator`` is not necessarily canonical nor is it filtered
in any way: it records the assumptions used to instantiate a Symbol
and (for storage purposes) represents a more compact representation
of the assumptions needed to recreate the full set in
`Symbol.assumptions0`.


References
==========

.. [1] https://en.wikipedia.org/wiki/Negative_number
.. [2] https://en.wikipedia.org/wiki/Parity_%28mathematics%29
.. [3] https://en.wikipedia.org/wiki/Imaginary_number
.. [4] https://en.wikipedia.org/wiki/Composite_number
.. [5] https://en.wikipedia.org/wiki/Irrational_number
.. [6] https://en.wikipedia.org/wiki/Prime_number
.. [7] https://en.wikipedia.org/wiki/Finite
.. [8] https://docs.python.org/3/library/math.html#math.isfinite
.. [9] http://docs.scipy.org/doc/numpy/reference/generated/numpy.isfinite.html
.. [10] https://en.wikipedia.org/wiki/Transcendental_number
.. [11] https://en.wikipedia.org/wiki/Algebraic_number

"""

from sympy.core.facts import FactRules, FactKB
from sympy.core.core import BasicMeta

from random import shuffle

_assume_rules = FactRules([
# integer domain:
    'integer        ->  rational',
    'integer        ==  extended_integer & finite',
    'integer        ->  extended_integer',
    
    'zero           ->  even & finite',
    'zero           ==  extended_nonnegative & extended_nonpositive',
    'zero           ==  nonnegative & nonpositive',
    
    'prime          ->  integer & positive',
    'odd            ==  integer & !even',
    'even           ==  integer & !odd',

    'composite      ->  integer & positive & !prime',
    '!composite     ->  !positive | !even | prime',
    
    'extended_integer -> extended_rational',
    'extended_integer -> integer | infinite',
    'extended_integer -> super_integer',
    
    'super_integer -> super_rational',
        
# rational domain:    
    'rational       ->  real',
    'rational       ->  algebraic',
    'rational       ==  extended_rational & finite',
    
    'extended_rational -> extended_real',
    'extended_rational -> rational | infinite',
    'extended_rational -> hyper_rational',
    
    'hyper_rational -> hyper_real',
    'hyper_rational -> super_rational',
    'super_rational -> super_real',
    
# real domain:    
    'real           ->  hermitian',
    'real           ==  extended_real & finite',
    'real           ==  negative | zero | positive',
    'real           ->  extended_real',
    
    'negative       ==  nonpositive & nonzero',
    'positive       ==  nonnegative & nonzero',

    'nonpositive    ==  real & !positive',
    'nonnegative    ==  real & !negative',

    'positive       ==  extended_positive & finite',
    'negative       ==  extended_negative & finite',
    'nonpositive    ==  extended_nonpositive & finite',
    'nonnegative    ==  extended_nonnegative & finite',
    
    'irrational     ==  real & !rational',
    'noninteger     ==  extended_real & !integer',
    
    'extended_real  ->  extended_complex',
    'extended_real  ->  real | infinite',
    
    'extended_real        ==  extended_negative | zero | extended_positive',
    'extended_real        ->  hyper_real',
    
    'extended_negative    ==  extended_nonpositive & extended_nonzero',
    'extended_positive    ==  extended_nonnegative & extended_nonzero',

    'extended_nonpositive ==  extended_real & !extended_positive',
    'extended_nonnegative ==  extended_real & !extended_negative',
    
    'hyper_real -> super_real',
    'hyper_real -> hyper_complex',
    'super_real -> super_complex',
    
# complex domain:
    'complex        -> extended_complex',
    'complex        ==  extended_complex & finite',
    
    'algebraic      ->  complex',
    'transcendental ==  complex & !algebraic',
    'imaginary      ->  complex',
    'imaginary      ->  antihermitian',
    'imaginary      ->  !extended_real',
    
    'nonzero        ->  !zero',
    'nonzero        ->  extended_nonzero & finite',

    'infinite       ==  !finite',
    
    'extended_nonzero     ==  extended_complex & !zero',
    'extended_nonzero     ->  hyper_complex',
    
    'extended_complex ->  complex | infinite',
    'extended_complex ->  hyper_complex',
    'hyper_complex    ->  super_complex',
    
# matrix domain:
    'invertible == !singular',
# random domain:
    'random -> finite',
    'probable -> random',
    
# set domain:    
    'empty -> finiteset',
    'infiniteset == !finiteset',
    'nonempty == !empty',
    
    'finiteset -> countable',
    'countable -> measurable',
    'uncountable == !countable',
    'unmeasurable -> !measurable',
])

_assume_defined = _assume_rules.defined_facts.copy()
_assume_defined.add('polar')
_assume_defined = frozenset(_assume_defined)


def assumptions(expr, _check=None):
    """return the T/F assumptions of ``expr``"""
    n = sympify(expr)
    if n.is_Symbol:
        rv = n.assumptions0  # are any important ones missing?
        if _check is not None:
            rv = {k: rv[k] for k in set(rv) & set(_check)}
        return rv
    rv = {}
    for k in _assume_defined if _check is None else _check:
        v = getattr(n, 'is_{}'.format(k))
        if v is not None:
            rv[k] = v
    return rv


def common_assumptions(exprs, check=None):
    """return those assumptions which have the same True or False
    value for all the given expressions.

    Examples
    ========

    >>> from sympy.core.assumptions import common_assumptions
    >>> from sympy import oo, pi, sqrt
    >>> common_assumptions([-4, 0, sqrt(2), 2, pi, oo])
    {'commutative': True, 'composite': False,
    'extended_real': True, 'imaginary': False, 'odd': False}

    By default, all assumptions are tested; pass an iterable of the
    assumptions to limit those that are reported:

    >>> common_assumptions([0, 1, 2], ['positive', 'integer'])
    {'integer': True}
    """
    check = _assume_defined if check is None else set(check)
    if not check or not exprs:
        return {}

    # get all assumptions for each
    assume = [assumptions(i, _check=check) for i in sympify(exprs)]
    # focus on those of interest that are True
    for i, e in enumerate(assume):
        assume[i] = {k: e[k] for k in set(e) & check}
    # what assumptions are in common?
    common = set.intersection(*[set(i) for i in assume])
    # which ones hold the same value
    a = assume[0]
    return {k: a[k] for k in common if all(a[k] == b[k]
        for b in assume)}


def failing_assumptions(expr, **assumptions):
    """
    Return a dictionary containing assumptions with values not
    matching those of the passed assumptions.

    Examples
    ========

    >>> from sympy import failing_assumptions, Symbol

    >>> x = Symbol('x', real=True, positive=True)
    >>> y = Symbol('y')
    >>> failing_assumptions(6*x + y, real=True, positive=True)
    {'positive': None, 'real': None}

    >>> failing_assumptions(x**2 - 1, positive=True)
    {'positive': None}

    If *expr* satisfies all of the assumptions, an empty dictionary is returned.

    >>> failing_assumptions(x**2, positive=True)
    {}

    """
    expr = sympify(expr)
    failed = {}
    for k in assumptions:
        test = getattr(expr, 'is_%s' % k, None)
        if test is not assumptions[k]:
            failed[k] = test
    return failed  # {} or {assumption: value != desired}


def check_assumptions(expr, against=None, **assume):
    """
    Checks whether assumptions of ``expr`` match the T/F assumptions
    given (or possessed by ``against``). True is returned if all
    assumptions match; False is returned if there is a mismatch and
    the assumption in ``expr`` is not None; else None is returned.

    Explanation
    ===========

    *assume* is a dict of assumptions with True or False values

    Examples
    ========

    >>> from sympy import Symbol, pi, I, exp, check_assumptions
    >>> check_assumptions(-5, integer=True)
    True
    >>> check_assumptions(pi, real=True, integer=False)
    True
    >>> check_assumptions(pi, real=True, negative=True)
    False
    >>> check_assumptions(exp(I*pi/7), real=False)
    True
    >>> x = Symbol('x', real=True, positive=True)
    >>> check_assumptions(2*x + 1, real=True, positive=True)
    True
    >>> check_assumptions(-2*x - 5, real=True, positive=True)
    False

    To check assumptions of *expr* against another variable or expression,
    pass the expression or variable as ``against``.

    >>> check_assumptions(2*x + 1, x)
    True

    To see if a number matches the assumptions of an expression, pass
    the number as the first argument, else its specific assumptions
    may not have a non-None value in the expression:

    >>> check_assumptions(x, 3)
    >>> check_assumptions(3, x)
    True

    ``None`` is returned if ``check_assumptions()`` could not conclude.

    >>> check_assumptions(2*x - 1, x)

    >>> z = Symbol('z')
    >>> check_assumptions(z, real=True)

    See Also
    ========

    failing_assumptions

    """
    expr = sympify(expr)
    if against is not None:
        if assume:
            raise ValueError(
                'Expecting `against` or `assume`, not both.')
        assume = assumptions(against)
    known = True
    for k, v in assume.items():
        if v is None:
            continue
        e = getattr(expr, 'is_' + k, None)
        if e is None:
            known = None
        elif v != e:
            return False
    return known


class StdFactKB(FactKB):
    """A FactKB specialized for the built-in rules

    This is the only kind of FactKB that Basic objects should use.
    """

    def __init__(self, facts=None):
        super().__init__(_assume_rules)
        # save a copy of the facts dict
        if not facts:
            self._generator = {}
        elif not isinstance(facts, FactKB):
            self._generator = facts.copy()
        else:
            self._generator = facts.generator
        if facts:
            self.deduce_all_facts(facts)

    def copy(self):
        return self.__class__(self)

    @property
    def generator(self):
        return self._generator.copy()


def as_property(fact):
    """Convert a fact name to the name of the corresponding property"""
    return 'is_%s' % fact


def make_property(fact):
    """Create the automagic property corresponding to a fact."""

    def getit(self):
        try:
            return self._assumptions[fact]
        except KeyError:
            if self._assumptions is self.default_assumptions:
                self._assumptions = self.default_assumptions.copy()
            return self._ask(fact)

    return property(getit)


def _ask(fact, obj):
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
    assumptions = obj._assumptions
    handler_map = obj._prop_handler

    # Store None into the assumptions so that recursive attempts at
    # evaluating the same fact don't trigger infinite recursion.
    assumptions._tell(fact, None)

    # First try the assumption evaluation function if it exists
    try:
        evaluate = handler_map[fact]
    except KeyError:
        pass
    else:
        a = evaluate(obj)
        if a is not None:
#             assumptions.deduce_all_facts(((fact, a),))
            assumptions[fact] = a
            return a

    # Try assumption's prerequisites
    prereq = list(_assume_rules.prereq[fact])
    shuffle(prereq)
    for pk in prereq:
        if pk in assumptions:
            continue
        if pk in handler_map:
            _ask(pk, obj)

            # we might have found the value of fact
            ret_val = assumptions.get(fact)
            if ret_val is not None:
                return ret_val

    # Note: the result has already been cached
    return None


class ManagedProperties(BasicMeta):
    """Metaclass for classes with old-style assumptions"""

    is_IndexedOperator = False
    
    def __init__(cls, *args, **kws):
        BasicMeta.__init__(cls, *args, **kws)

        local_defs = {}
        for k in _assume_defined:
            attrname = as_property(k)
            v = cls.__dict__.get(attrname, '')
            if isinstance(v, (bool, int, type(None))):
                if v is not None:
                    v = bool(v)
                local_defs[k] = v

        defs = {}
        for base in reversed(cls.__bases__):
            assumptions = getattr(base, '_explicit_class_assumptions', None)
            if assumptions is not None:
                defs.update(assumptions)
        defs.update(local_defs)

        cls._explicit_class_assumptions = defs
        cls.default_assumptions = StdFactKB(defs)

        cls._prop_handler = {}
        for k in _assume_defined:
            eval_is_meth = getattr(cls, '_eval_is_%s' % k, None)
            if eval_is_meth is not None:
                cls._prop_handler[k] = eval_is_meth

        # Put definite results directly into the class dict, for speed
        for k, v in cls.default_assumptions.items():
            setattr(cls, as_property(k), v)

        # protection e.g. for Integer.is_even=F <- (Rational.is_integer=F)
        derived_from_bases = set()
        for base in cls.__bases__:
            default_assumptions = getattr(base, 'default_assumptions', None)
            # is an assumption-aware class
            if default_assumptions is not None:
                derived_from_bases.update(default_assumptions)

        for fact in derived_from_bases - set(cls.default_assumptions):
            pname = as_property(fact)
            if pname not in cls.__dict__:
                setattr(cls, pname, make_property(fact))

        # Finally, add any missing automagic property (e.g. for Basic)
        for fact in _assume_defined:
            pname = as_property(fact)
            if not hasattr(cls, pname):
                setattr(cls, pname, make_property(fact))

        pname = as_property(cls.__name__)
        if pname not in cls.__dict__: 
            setattr(cls, pname, True)
        
#         look in Method Resolution Order
        for base in reversed(cls.__mro__):
            if not isinstance(base, ManagedProperties):
                continue
        
            assert base.__name__ == 'Basic', "cls = %s, base = %s" % (cls, base)
            if pname not in base.__dict__:
                setattr(base, pname, False)
            break
        
    def process_limit(self, limit):
        if isinstance(limit, slice): 
            x, a, b = limit.start, limit.stop, limit.step
            if b is not None:
                return x, a, b
            
            if isinstance(a, set) or self.is_Punctured:
                return x, a
            
            if isinstance(a, int) or a.type.is_DtypeInteger or a.is_Infinity:
                return x, 0, a
            
            return x, a

        return limit,
        
    def __getitem__(self, limits):
        return IndexedOperator(
            self, 
            [self.process_limit(limit) for limit in limits] if isinstance(limits, tuple) else [self.process_limit(limits)])

    def __iter__(self):
        raise TypeError

    @property
    def is_FunctionClass(self):
        return self.is_Application
    

# in the form of : Stack[Tuple[2]], BlockMatrix[1][Identity @ Expr]
class IndexedOperator:
    is_Basic = False
    is_IndexedOperator = True
    is_Number = False
    is_Wanted = False
    
    def __init__(self, cls, limits, supIndex=None):
        self.cls = cls
        self.limits = limits
        self._basic = None
        self.supIndex = supIndex

    def __call__(self, *args, **kwargs):
        if (supIndex := self.supIndex) is not None:
            kwargs['supIndex'] = supIndex
        return self.cls(*args, *self.limits, **kwargs)
        
    def has_int_index(self):
        limits = self.limits
        if len(limits) == 1:
            children = limits[0]
            if len(children) == 1:
                child = children[0]
                return isinstance(child, int) and child > 1
            
    @property
    def basic(self):
        if self._basic is None: 
            cls = self.cls
            limits = self.limits
            assert isinstance(cls, type)
            from sympy.core.of import Basic, sympify
            kwargs = {}            
            if len(limits) == 1: 
                children = limits[0]
                
                if len(children) == 1: 
                    child = children[0]
                    if isinstance(child, int):
                        if child > 1:
                            children = [cls] * child
                            children[-1] = ~cls

                            if hasattr(cls.__mro__[-3], 'is_Basic'):
                                cls = cls.__mro__[-3]
                            else:
                                cls = cls.__mro__[-4]
                            assert cls.is_Basic
                        else:
                            if child == 1 and cls.is_BlockMatrix:
                                children = []
                                kwargs['axis'] = 1
                            else:
                                children = [sympify(child)]
                    elif isinstance(child, IndexedOperator):
                        if child.has_int_index():
                            child = child.basic
                            children = [*child.args]
                            children[-1] = children[-1].func
                            
            else:
                children = []                
                for limit in limits: 
                    assert len(limit) == 1
                    child = limit[0]
                    if isinstance(child, IndexedOperator) and child.has_int_index():
                        child = child.basic
                        child = [*child.args]
                        child[-1] = child[-1].func
                        children.extend(child)
                    else:
                        children.append(sympify(child))
            
            obj = Basic.__new__(cls, *children, **kwargs)
            self._basic = obj
        return self._basic
        
    def __invert__(self):
        from sympy.core.core import Wanted
        return Wanted(self.basic)
    
    @property
    def unwanted(self):
        return self.basic.unwanted

    def __repr__(self):
        return repr(self.basic)
    
    __str__ = __repr__
        
    def __getattr__(self, attr):
        return getattr(self.basic, attr)

    def __getitem__(self, indices):
        [*axis] = self.limits
        axis = tuple(axis for axis, in axis)
        if len(axis) == 1:
            axis, = axis
            if self.func.__name__ == 'Basic' and isinstance(axis, int) and axis > 1:
                args = self.args
                assert args[-1].is_Wanted
                last = args[-1].func[indices]
                if isinstance(indices, type) or not indices.is_wanted():
                    last = ~last 
                return self.func[args[:-1] + (last,)]

        if isinstance(indices, tuple):
            args = self.func, *indices
        elif isinstance(indices, int) and indices > 1:
            from sympy.core import Basic
            return Basic[(self.unwanted,) * (indices - 1) + (~self,)]
        else:
            args = self.func, indices
        from sympy.core.of import Basic
        return Basic.__new__(*args, axis=axis)
        
    def __pow__(self, other): 
        return BasicMeta.__pow__(self.basic, other)
    
    def __neg__(self): 
        return BasicMeta.__neg__(self.basic)
    
    def __sub__(self, other): 
        return BasicMeta.__sub__(self.basic, other)
    
    def __add__(self, other): 
        return BasicMeta.__add__(self.basic, other)
    
    def __mul__(self, other): 
        return BasicMeta.__mul__(self.basic, other)
    
    def __mod__(self, other): 
        return BasicMeta.__mod__(self.basic, other)
    
    def __truediv__(self, other): 
        return BasicMeta.__truediv__(self.basic, other)
    
    def __floordiv__(self, other): 
        return BasicMeta.__floordiv__(self.basic, other)
    
    def __matmul__(self, other): 
        return BasicMeta.__matmul__(self.basic, other)
    
    def __gt__(self, other): 
        return BasicMeta.__gt__(self.basic, other)

    def __ge__(self, other): 
        return BasicMeta.__ge__(self.basic, other)

    def __lt__(self, other): 
        return BasicMeta.__lt__(self.basic, other)

    def __le__(self, other): 
        return BasicMeta.__le__(self.basic, other)

    def __or__(self, other): 
        return BasicMeta.__or__(self.basic, other)

    def __and__(self, other): 
        return BasicMeta.__and__(self.basic, other)

    def __rsub__(self, lhs):
        from sympy import sympify
        lhs = sympify(lhs)
        return BasicMeta.__sub__(lhs, self.basic)
    
    def __radd__(self, lhs):
        from sympy import sympify
        lhs = sympify(lhs)
        return BasicMeta.__add__(lhs, self.basic)
    
    def __rmul__(self, lhs):
        from sympy import sympify
        lhs = sympify(lhs)
        return BasicMeta.__mul__(lhs, self.basic)

    def __rtruediv__(self, lhs):
        from sympy import sympify
        lhs = sympify(lhs)
        return BasicMeta.__truediv__(lhs, self.basic)

    def __rfloordiv__(self, lhs):
        from sympy import sympify
        lhs = sympify(lhs)
        return BasicMeta.__floordiv__(lhs, self.basic)

    def __rmatmul__(self, other): 
        return BasicMeta.__rmatmul__(self.basic, other)

    def __xor__(self, other):
        limits = self.limits
        supIndex = len(limits)
        limits = [*limits, (other,)]
        return IndexedOperator(self.cls, limits, supIndex)

