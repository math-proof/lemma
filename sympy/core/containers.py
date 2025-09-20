"""Module for SymPy containers

    (SymPy objects that store other SymPy objects)

    The containers implemented in this module are subclassed to Basic.
    They are supposed to work seamlessly within the SymPy framework.
"""

from collections import OrderedDict

from sympy.core.basic import Basic
from sympy.core.compatibility import as_int, MutableSet
from sympy.core.sympify import sympify, converter
from sympy.utilities.iterables import iterable
from sympy.core.logic import fuzzy_or
from sympy.core.cache import cacheit


class Tuple(Basic):
    """
    Wrapper around the builtin tuple object

    The Tuple is a subclass of Basic, so that it works well in the
    SymPy framework.  The wrapped tuple is available as self.args, but
    you can also access elements or slices with [:] syntax.

    Parameters
    ==========

    sympify : bool
        If ``False``, ``sympify`` is not called on ``args``. This
        can be used for speedups for very large tuples where the
        elements are known to already be sympy objects.

    Example
    =======

    >>> from sympy import symbols
    >>> from sympy.core.containers import Tuple
    >>> a, b, c, d = symbols('a b c d')
    >>> Tuple(a, b, c)[1:]
    (b, c)
    >>> Tuple(a, b, c).subs(a, d)
    (d, b, c)

    """

    def __new__(cls, *args, **kwargs):
        if kwargs.get('sympify', True):
            args = (sympify(arg) for arg in args)
        obj = Basic.__new__(cls, *args)
        return obj

    def __getitem__(self, i):
        if isinstance(i, slice):
            indices = i.indices(len(self))
            return Tuple(*(self.args[j] for j in range(*indices)))
        return self.args[i]

    def __len__(self):
        return len(self.args)

    def __contains__(self, item):
        return item in self.args

    def __iter__(self):
        return iter(self.args)

    def __add__(self, other):
        if isinstance(other, Tuple):
            return Tuple(*(self.args + other.args))
        elif isinstance(other, tuple):
            return Tuple(*(self.args + other))
        else:
            return NotImplemented

    def __radd__(self, other):
        if isinstance(other, Tuple):
            return Tuple(*(other.args + self.args))
        elif isinstance(other, tuple):
            return Tuple(*(other + self.args))
        else:
            return NotImplemented

    def __mul__(self, other):
        try:
            n = as_int(other)
        except ValueError:
            raise TypeError("Can't multiply sequence by non-integer of type '%s'" % type(other))
        return self.func(*(self.args * n))

    __rmul__ = __mul__

    def __eq__(self, other):
        if isinstance(other, Basic):
            return super(Tuple, self).__eq__(other)
        return self.args == other

    def __ne__(self, other):
        if isinstance(other, Basic):
            return super(Tuple, self).__ne__(other)
        return self.args != other

    def __hash__(self):
        return hash(self.args)

    def _to_mpmath(self, prec):
        return tuple(a._to_mpmath(prec) for a in self.args)

    def __lt__(self, other):
        return sympify(self.args < other.args)

    def __le__(self, other):
        return sympify(self.args <= other.args)

    # XXX: Basic defines count() as something different, so we can't
    # redefine it here. Originally this lead to cse() test failure.
    def tuple_count(self, value):
        """T.count(value) -> integer -- return number of occurrences of value"""
        return self.args.count(value)

    def index(self, value, start=None, stop=None):
        """T.index(value, [start, [stop]]) -> integer -- return first index of value.
           Raises ValueError if the value is not present."""
        # XXX: One would expect:
        #
        # return self.args.index(value, start, stop)
        #
        # here. Any trouble with that? Yes:
        #
        # >>> (1,).index(1, None, None)
        # Traceback (most recent call last):
        #   File "<stdin>", line 1, in <module>
        # TypeError: slice indices must be integers or None or have an __index__ method
        #
        # See: http://bugs.python.org/issue13340

        if start is None and stop is None:
            return self.args.index(value)
        elif stop is None:
            return self.args.index(value, start)
        else:
            return self.args.index(value, start, stop)

    @cacheit
    def _eval_domain_defined(self, x, **_):
        domain = Basic._eval_domain_defined(self, x)
        for arg in self.args:
            domain &= arg.domain_defined(x)
        return domain

    def _format_ineq(self, p, **kwargs):
        match p.printmethod:
            case '_latex':
                if len(self) == 3:
                    x, a, b = self
                    if b.is_set:
                        return r"%s \in %s \left| %s \right. " % (p._print(x), p._print(b), p._print(a))
                    if x.is_integer:
                        if b.is_Add and b.args[0].is_One:
                            return r"%s \leq %s \leq %s" % tuple([p._print(s) for s in (a, x, b - 1)])
                        else:
                            return r"%s \leq %s \lt %s" % tuple([p._print(s) for s in (a, x, b)])
                    return r"%s \lt %s \lt %s" % tuple([p._print(s) for s in (a, x, b)])
                elif len(self) == 2:
                    x, cond = self
                    if cond.is_set:
                        return r"%s \in %s" % (p._print(x), p._print(cond))
                    if cond.is_BinaryCondition and cond.lhs == x:
                        return p._print(cond)
                    return r"%s \left| %s \right. " % (p._print(x), p._print(cond))
                else:
                    return p._print(self[0])
            case '_sympystr':
                if len(self) == 3:
                    if self[1].is_zero:
                        return r"%s:%s" % tuple([p._print(s) for s in (self[0], self[2])])
                    else:
                        return r"%s:%s:%s" % tuple([p._print(s) for s in (self[0], self[1], self[2])])
                elif len(self) == 2:
                    e, s = self
                    if s.is_Range:
                        start, stop, *step = s.args
                        if step:
                            step, = step
                        else:
                            step = 1

                        if step == 1:
                            if start.is_Zero:
                                return r"%s:%s" % tuple([p._print(s) for s in (e, stop)])
                            return r"%s:%s:%s" % tuple([p._print(s) for s in (e, start, stop)])
                    return r"%s:%s" % tuple([p._print(s) for s in (e, self[1])])
                else:
                    return p._print(self[0])
            case '_lean':
                if len(self) == 3:
                    from sympy import Function
                    x, a, b = self
                    x = p._print(x)
                    if b.is_set:
                        S, cond = p._print(b), p._print(a)
                        return f"{x} ∈ {S} | {cond}"
                    if self[0].is_integer:
                        if b.is_Add and b.args[0].is_One:
                            return f"{x} ∈ {Function.lean_fun('Icc', a, b - 1, p=p)}"
                        else:
                            if a == 0:
                                if kwargs.get('lt'):
                                    return f"{x} < {b}"
                                return f"{x} : {Function.lean_fun('Fin', b, p=p)}"
                            else:
                                return f"{x} ∈ {Function.lean_fun('Ico', a, b, p=p)}"
                    return f"{x} ∈ {Function.lean_fun('Ioo', a, b, p=p)}"
                elif len(self) == 2:
                    x, cond = self
                    if cond.is_set:
                        x, S = p._print(x), p._print(cond)
                        return f"{x} ∈ {S}"
                    if cond.is_BinaryCondition and cond.lhs == x:
                        return p._print(cond)
                    x, cond = p._print(x), p._print(cond)
                    return f"{x} | {cond}"
                else:
                    return p._print(self[0])
            case _:
                if len(self) == 3:
                    if self[1].is_zero:
                        return r"%s:%s" % tuple([str(s) for s in (self[0], self[2])])
                    else:
                        return r"%s:%s:%s" % tuple([str(s) for s in (self[0], self[1], self[2])])
                elif len(self) == 2:
                    return r"%s:%s" % tuple([str(s) for s in (self[0], self[1])])
                else:
                    return str(self[0])

    def domain_latex(self, domain=None):
        if domain.is_Range:
            start, end = domain.start, domain.stop
            if end.is_Infinity:
                if start.is_NegativeInfinity:
                    return r"%s\in%s" % (self.latex, r'\mathbb{Z}')
                return r"%s \ge %s" % (self.latex, start.latex)
            else:
                if start.is_NegativeInfinity:
                    return r"%s < %s" % (self.latex, end.latex)
                return r"%s \le %s < %s" % (start.latex, self.latex, end.latex)
            
        elif domain.is_Interval:
            start, end = domain.start, domain.stop
            if end.is_Infinity:
                if start.is_NegativeInfinity:
                    return r"%s\in%s" % (self.latex, r'\mathbb{R}')
                if domain.left_open:
                    return r"%s > %s" % (self.latex, start.latex)
                return r"%s \ge %s" % (self.latex, start.latex)
            else:
                if start.is_NegativeInfinity:
                    if domain.right_open:
                        return r"%s < %s" % (self.latex, end.latex)
                    return r"%s \le %s" % (self.latex, end.latex)

                if domain.left_open:
                    if domain.right_open:
                        return r"%s < %s < %s" % (start.latex, self.latex, end.latex)
                    return r"%s < %s \le %s" % (start.latex, self.latex, end.latex)
                if domain.right_open:
                    return r"%s \le %s < %s" % (start.latex, self.latex, end.latex)
                return r"%s \le %s \le %s" % (start.latex, self.latex, end.latex)
        elif domain.is_bool:
            return r"%s : %s" % (self.latex, domain.latex)
        else:
            return r"%s \in %s" % (self.latex, domain.latex)

    def _eval_is_random(self):
        return fuzzy_or(arg.is_random for arg in self.args)
    
    def _subs_limits(self, old, new):
        hit = False
        x, *ab = self
        for j, t in enumerate(ab):
            _t = t._subs(old, new)
            if t != _t:
                hit = True
                ab[j] = _t
                
        if x.is_Indexed or x.is_Sliced:
            _hit = False
            indices = [*x.indices]
            for j, t in enumerate(indices):
                _t = t._subs(old, new)
                if t != _t:
                    _hit = True
                    indices[j] = _t
            if _hit:
                x = x.func(x.base, *indices)
                hit = True
        
        if hit:
            return self.func(x, *ab)
        return self

    @property
    def is_intlimit(self):
        x, *ab = self
        return x.is_integer and len(ab) == 2 and not x.shape and not x.is_set

    def to_setlimit(self):
        x, *ab = self
        if len(ab) == 2 and not ab[1].is_set:
            return x, x.range(*ab)
        if not ab:
            return x, x.universalSet
        return self
    
    @property
    def slice_args(self):
        start, stop, *step = self
        if step:
            [step] = step
        else:
            step = 1
        return start, stop, step
    
    @property
    def slice(self):
        return slice(*self.slice_args)

    @classmethod
    def from_slice(cls, slice, size=None):
        start, stop, step = slice.start, slice.stop, slice.step
        if start is None:
            start = 0
            
        if stop is None:
            if size:
                stop = size
            
        if step is None:
            step = 1
            
        return cls(start, stop) if step == 1 else cls(start, stop, step)
        
    @classmethod
    def as_setlimit(cls, self):
        x, *ab = self
        if len(ab) == 2 and not ab[1].is_set:
            return x, x.range(*ab)
        return self

    @classmethod
    def to_coerce_setlimit(cls, self, function=None, dir=None):
        x, *ab = self
        if not ab:
            if function is None:
                domain = x.universalSet
            else:
                domain = function.domain_defined(x)
        elif len(ab) == 1: 
            domain = ab[0]
            if domain.is_bool:
                domain = x.domain_conditioned(domain)
        else:
            a, b = ab
            if b.is_set:
                domain = b & x.domain_conditioned(a)
            else:
                if x.is_integer:
                    from sympy import Range
                    domain = Range(a, b)
                else:
                    from sympy import Interval
                    if dir:
                        if a <= b:
                            return x, Interval.open(a, b), 1
                        elif a > b:
                            return x, Interval.open(b, a), -1
                        else:
                            return

                    return x, Interval.open(a, b)
        return x, domain

    def coerce_setlimit(self, function=None):
        return Tuple.to_coerce_setlimit(self, function)
    
    def limit(self, x, xlim, dir=1):
        """ Compute limit x->xlim.
        """
        from sympy.series.limits import limit
        return Tuple(*[limit(f, x, xlim, dir) for f in self.args])
    
    @classmethod
    def is_nonemptyset(cls, limits):
        for limit in limits:
            args = Tuple.to_coerce_setlimit(limit)
            if not args:
                continue

            x, domain, *dir = args
            if not domain.is_nonempty:
                return False

        return True
    
    def _sympystr(self, p):
        return p._print_tuple(self)

    def _lean(self, p):
        return p._print_tuple(self)
    
    def _latex(self, p):
        return p._print_tuple(self)

    def dtype(self):
        from sympy.core.symbol import DtypeTuple
        return DtypeTuple(*(arg.dtype for arg in self.args))


converter[tuple] = lambda args: Tuple(*args)


def tuple_wrapper(method):
    """
    Decorator that converts any tuple in the function arguments into a Tuple.

    The motivation for this is to provide simple user interfaces.  The user can
    call a function with regular tuples in the argument, and the wrapper will
    convert them to Tuples before handing them to the function.

    >>> from sympy.core.containers import tuple_wrapper
    >>> def f(*args):
    ...    return args
    >>> g = tuple_wrapper(f)

    The decorated function g sees only the Tuple argument:

    >>> g(0, (1, 2), 3)
    (0, (1, 2), 3)

    """

    def wrap_tuples(*args, **kw_args):
        newargs = []
        for arg in args:
            if type(arg) is tuple:
                newargs.append(Tuple(*arg))
            else:
                newargs.append(arg)
        return method(*newargs, **kw_args)

    return wrap_tuples


class Dict(Basic):
    """
    Wrapper around the builtin dict object

    The Dict is a subclass of Basic, so that it works well in the
    SymPy framework.  Because it is immutable, it may be included
    in sets, but its values must all be given at instantiation and
    cannot be changed afterwards.  Otherwise it behaves identically
    to the Python dict.

    >>> from sympy.core.containers import Dict

    >>> D = Dict({1: 'one', 2: 'two'})
    >>> for key in D:
    ...    if key == 1:
    ...        print('%s %s' % (key, D[key]))
    1 one

    The args are sympified so the 1 and 2 are Integers and the values
    are Symbols. Queries automatically sympify args so the following work:

    >>> 1 in D
    True
    >>> D.has('one') # searches keys and values
    True
    >>> 'one' in D # not in the keys
    False
    >>> D[1]
    one

    """

    def __new__(cls, *args):
        if len(args) == 1 and isinstance(args[0], (dict, Dict)):
            items = [Tuple(k, v) for k, v in args[0].items()]
        elif iterable(args) and all(len(arg) == 2 for arg in args):
            items = [Tuple(k, v) for k, v in args]
        else:
            raise TypeError('Pass Dict args as Dict((k1, v1), ...) or Dict({k1: v1, ...})')
        elements = frozenset(items)
        obj = Basic.__new__(cls, elements)
        obj.elements = elements
        obj._dict = dict(items)  # In case Tuple decides it wants to sympify
        return obj

    def __getitem__(self, key):
        """x.__getitem__(y) <==> x[y]"""
        return self._dict[sympify(key)]

    def __setitem__(self, key, value):
        raise NotImplementedError("SymPy Dicts are Immutable")

    @property
    def args(self):
        return tuple(self.elements)

    def items(self):
        '''D.items() -> list of D's (key, value) pairs, as 2-tuples'''
        return self._dict.items()

    def keys(self):
        '''D.keys() -> list of D's keys'''
        return self._dict.keys()

    def values(self):
        '''D.values() -> list of D's values'''
        return self._dict.values()

    def __iter__(self):
        '''x.__iter__() <==> iter(x)'''
        return iter(self._dict)

    def __len__(self):
        '''x.__len__() <==> len(x)'''
        return self._dict.__len__()

    def get(self, key, default=None):
        '''D.get(k[,d]) -> D[k] if k in D, else d.  d defaults to None.'''
        return self._dict.get(sympify(key), default)

    def __contains__(self, key):
        '''D.__contains__(k) -> True if D has a key k, else False'''
        return sympify(key) in self._dict

    def __lt__(self, other):
        return sympify(self.args < other.args)

    @property
    def _sorted_args(self):
        from sympy.utilities import default_sort_key
        return tuple(sorted(self.args, key=default_sort_key))


class OrderedSet(MutableSet):

    def __init__(self, iterable=None):
        if iterable:
            self.map = OrderedDict((item, None) for item in iterable)
        else:
            self.map = OrderedDict()

    def __len__(self):
        return len(self.map)

    def __contains__(self, key):
        return key in self.map

    def add(self, key):
        self.map[key] = None

    def discard(self, key):
        self.map.pop(key)

    def pop(self, last=True):
        return self.map.popitem(last=last)[0]

    def __iter__(self):
        for key in self.map.keys():
            yield key

    def __repr__(self):
        if not self.map:
            return '%s()' % (self.__class__.__name__,)
        return '%s(%r)' % (self.__class__.__name__, list(self.map.keys()))

    def intersection(self, other):
        result = []
        for val in self:
            if val in other:
                result.append(val)
        return self.__class__(result)

    def difference(self, other):
        result = []
        for val in self:
            if val not in other:
                result.append(val)
        return self.__class__(result)

    def update(self, iterable):
        for val in iterable:
            self.add(val)
