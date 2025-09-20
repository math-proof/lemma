from sympy.core.assumptions import StdFactKB, ManagedProperties
from sympy.core.compatibility import is_sequence, ordered, NotIterable
from .basic import Basic, Atom
from .sympify import sympify
from .singleton import S
from .expr import Expr, AtomicExpr
from .cache import cacheit
from sympy.core.logic import fuzzy_bool
from sympy.utilities.iterables import cartes
from sympy.core.containers import Tuple

import string, random, re
from sympy.logic.boolalg import BooleanAtom, Imply, Given


class Str(Atom):
    """
    Represents string in SymPy.

    Explanation
    ===========

    Previously, ``Symbol`` was used where string is needed in ``args`` of SymPy
    objects, e.g. denoting the name of the instance. However, since ``Symbol``
    represents mathematical scalar, this class should be used instead.

    """
    __slots__ = ('name',)

    def __new__(cls, name, **kwargs):
        if not isinstance(name, str):
            raise TypeError("name should be a string, not %s" % repr(type(name)))
        obj = Expr.__new__(cls, **kwargs)
        obj.name = name
        return obj

    def __getnewargs__(self):
        return (self.name,)

    def _hashable_content(self):
        return (self.name,)


def _filter_assumptions(kwargs):
    """Split the given dict into assumptions and non-assumptions.
    Keys are taken as assumptions if they correspond to an
    entry in ``_assume_defined``.
    """
    assumptions, nonassumptions = map(dict, sift(kwargs.items(),
        lambda i: i[0] in _assume_defined,
        binary=True))
    Symbol._sanitize(assumptions)
    return assumptions, nonassumptions


def _symbol(s, matching_symbol=None, **assumptions):
    """Return s if s is a Symbol, else if s is a string, return either
    the matching_symbol if the names are the same or else a new symbol
    with the same assumptions as the matching symbol (or the
    assumptions as provided).

    Examples
    ========

    >>> from sympy import Symbol
    >>> from sympy.core.symbol import _symbol
    >>> _symbol('y')
    y
    >>> _.is_real is None
    True
    >>> _symbol('y', real=True).is_real
    True

    >>> x = Symbol('x')
    >>> _symbol(x, real=True)
    x
    >>> _.is_real is None  # ignore attribute if s is a Symbol
    True

    Below, the variable sym has the name 'foo':

    >>> sym = Symbol('foo', real=True)

    Since 'x' is not the same as sym's name, a new symbol is created:

    >>> _symbol('x', sym).name
    'x'

    It will acquire any assumptions give:

    >>> _symbol('x', sym, real=False).is_real
    False

    Since 'foo' is the same as sym's name, sym is returned

    >>> _symbol('foo', sym)
    foo

    Any assumptions given are ignored:

    >>> _symbol('foo', sym, real=False).is_real
    True

    NB: the symbol here may not be the same as a symbol with the same
    name defined elsewhere as a result of different assumptions.

    See Also
    ========

    sympy.core.symbol.Symbol

    """
    if isinstance(s, str):
        if matching_symbol and matching_symbol.name == s:
            return matching_symbol
        return Symbol(s, **assumptions)
    elif isinstance(s, Symbol):
        return s
    else:
        raise ValueError('symbol must be string for symbol name or Symbol')


def _uniquely_named_symbol(xname, exprs=(), compare=str, modify=None, **assumptions):
    """Return a symbol which, when printed, will have a name unique
    from any other already in the expressions given. The name is made
    unique by prepending underscores (default) but this can be
    customized with the keyword 'modify'.

    Parameters
    ==========

        xname : a string or a Symbol (when symbol xname <- str(xname))
        compare : a single arg function that takes a symbol and returns
            a string to be compared with xname (the default is the str
            function which indicates how the name will look when it
            is printed, e.g. this includes underscores that appear on
            Dummy symbols)
        modify : a single arg function that changes its string argument
            in some way (the default is to preppend underscores)

    Examples
    ========

    >>> from sympy.core.symbol import _uniquely_named_symbol as usym, Dummy
    >>> from sympy.abc import x
    >>> usym('x', x)
    _x
    """
    default = None
    if is_sequence(xname):
        xname, default = xname
    x = str(xname)
    if not exprs:
        return _symbol(x, default, **assumptions)
    if not is_sequence(exprs):
        exprs = [exprs]
    syms = set().union(*[e.free_symbols for e in exprs])
    if modify is None:
        modify = lambda s: '_' + s
    while any(x == compare(s) for s in syms):
        x = modify(x)
    return _symbol(x, default, **assumptions)


class Symbol(AtomicExpr, NotIterable):
    """
    >>> a, b, c = Symbol(real=True)
    >>> (b - sqrt(b * b - 4 * a * c)) / (2 * a)
    """

    is_comparable = False

    __slots__ = ['name']

    is_symbol = True
    _explicit_class_assumptions = {}
    
    def intersection_sets(self, b):
        if b.is_ConditionSet:
            from sympy.sets import conditionset
            return conditionset(b.variable, b.condition, b.base_set & self)
        definition = self.definition
        if definition is not None:
            if definition in b:
                return self

    def union_sets(self, b):
        definition = self.definition
        if definition is not None:
            if definition in b:
                return b

    def __contains__(self, other): 
        contains = self.contains_with_subset(other)
        if contains is not None:
            return contains
        
        if self.definition is not None:
            return other in self.definition
        
        if other.is_Symbol:
            domain = other.domain_assumed
            if domain is not None:
                return domain in self

# precondition, self and other are structurally equal!
    def _dummy_eq(self, other):
        return self == other

    def structurally_equal(self, other):
        from sympy.tensor.indexed import Sliced, Indexed
        if isinstance(other, (Symbol, Indexed, Sliced)):
            return self.shape == other.shape
        return False

    @staticmethod
    def process_assumptions(assumptions, integer):
        domain = assumptions.get('domain')
        if domain is not None:
            from sympy import Interval, Range
            if isinstance(domain, list):
                domain = (Range if integer else Interval.open)(*domain)
               
            if isinstance(domain, set):
                assumptions['domain'] = sympify(domain) 
            elif isinstance(domain, type):
                assumptions['domain'] = domain
            elif domain.is_Range:
                if domain.start is S.NegativeInfinity:
                    if domain.stop is S.Infinity:
                        assumptions.pop('domain')
                    elif domain.stop is S.Zero:
                        assumptions.pop('domain')
                        assumptions['negative'] = True
                elif domain.start is S.Zero:
                    if domain.stop is S.Infinity:
                        assumptions.pop('domain')
                        assumptions['nonnegative'] = True
                elif domain.start is S.One:
                    if domain.stop is S.Infinity:
                        assumptions.pop('domain')
                        assumptions['positive'] = True
                        
            elif domain.is_Interval:
                if domain.start is S.NegativeInfinity:
                    if domain.stop is S.Infinity:
                        assumptions.pop('domain')
                        assumptions['real'] = True
                    elif domain.stop is S.Zero:
                        assumptions.pop('domain')
                        if domain.right_open:
                            assumptions['negative'] = True
                        else:
                            assumptions['nonpositive'] = True
                elif domain.start is S.Zero:
                    if domain.stop is S.Infinity:
                        assumptions.pop('domain')
                        if domain.left_open:
                            assumptions['positive'] = True
                        else:
                            assumptions['nonnegative'] = True
            elif domain.is_ComplexRegion:
                if domain == S.Complexes:
                    assumptions.pop('domain')
                    assumptions['complex'] = True

            if 'domain' not in assumptions:
                assumptions['integer'] = integer
        
    def copy(self, **kwargs):
        if not kwargs:
            return self
        
        if 'domain' in kwargs and len(kwargs) == 1 and kwargs['domain'] is not None:
            domain = kwargs['domain']
            kwargs.update(self.assumptions_hashable())
            kwargs['domain'] = domain
            return self.func(self.name, **kwargs)
        
        integer, rational, real, shape, dtype = self.is_integer, self.is_rational, self.is_real, self.shape, self.etype
        kwargs['integer'] = integer
        kwargs['rational'] = rational
        kwargs['real'] = real
        kwargs['shape'] = shape if shape else None
        kwargs['etype'] = dtype
        
        self.process_assumptions(kwargs, integer)
        return self.func(self.name, **kwargs)
    
    @property
    def unbounded(self):
        if self.is_bounded:
            return self.copy(domain=None)
        return self

    @property
    def _diff_wrt(self):
        """Allow derivatives wrt Symbols.

        Examples
        ========

            >>> from sympy import Symbol
            >>> x = Symbol('x')
            >>> x._diff_wrt
            True
        """
        return True

    def image_set(self):
        definition = self.definition
        if definition is not None: 
            return definition.image_set()

    def condition_set(self):
        definition = self.definition
        if definition is None:
            return
        return definition.condition_set()

    @staticmethod
    def _sanitize(assumptions, obj=None):
        """Remove None, covert values to bool, check commutativity *in place*.
        """
        # sanitize other assumptions so 1 -> True and 0 -> False
        for key in list(assumptions.keys()):
            from collections import defaultdict
            from sympy.utilities.exceptions import SymPyDeprecationWarning
            keymap = defaultdict(lambda: None)
            keymap.update({'bounded': 'finite', 'unbounded': 'infinite', 'infinitesimal': 'zero'})
            if keymap[key]:
                SymPyDeprecationWarning(
                    feature="%s assumption" % key,
                    useinstead="%s" % keymap[key],
                    issue=8071,
                    deprecated_since_version="0.7.6").warn()
                assumptions[keymap[key]] = assumptions[key]
                assumptions.pop(key)
                key = keymap[key]

            v = assumptions[key]
            if v is None:
                assumptions.pop(key)
                continue

            if key == 'shape':
                assumptions[key] = tuple(sympify(s) for s in v)
            elif key not in {'domain', 'definition', 'etype', 'distribution'}:
                assumptions[key] = bool(v)

        integer = assumptions.get('integer')
        if integer is None:
            domain = assumptions.get('domain')
            if domain is None:
                return
            else:
                integer = domain.etype.is_integer
                         
        Symbol.process_assumptions(assumptions, integer)
        
    def __new__(cls, *args, **assumptions):
        """Symbols are identified by name and assumptions::

        >>> from sympy import Symbol
        >>> Symbol("x") == Symbol("x")
        True
        >>> Symbol("x", real=True) == Symbol("x", real=False)
        False

        """
        cls._sanitize(assumptions, cls)
        if len(args) == 1:
            arg, = args
            if isinstance(arg, (str, tuple)):
                name = arg
            else:
                assumptions['definition'] = arg
                name = None
        elif len(args) == 2:
            name, definition = args
            assumptions['definition'] = definition
        else:
            name = None
            
        if name is None:
            import traceback
            line = traceback.extract_stack()[-2].line
            name = re.match(r'(.+?) *= *Symbol\(.+ *$', line)[1]
            if ',' in name:
                return (Symbol(name.strip(), **assumptions) for name in name.split(','))
            
        return Symbol.__xnew__(cls, name, **assumptions)

    def __new_stage2__(cls, name, **assumptions):
        obj = Expr.__new__(cls)
        obj.name = name
        # TODO: Issue #8873: Forcing the commutative assumption here means
        # later code such as ``srepr()`` cannot tell whether the user
        # specified ``commutative=True`` or omitted it.  To workaround this,
        # we keep a copy of the assumptions dict, then create the StdFactKB,
        # and finally overwrite its ``._generator`` with the dict copy.  This
        # is a bit of a hack because we assume StdFactKB merely copies the
        # given dict as ``._generator``, but future modification might, e.g.,
        # compute a minimal equivalent assumption set.
        tmp_asm_copy = assumptions.copy()

        # be strict about commutativity
        is_commutative = fuzzy_bool(assumptions.get('commutative', True))                
        assumptions['commutative'] = is_commutative
        obj._assumptions = StdFactKB(assumptions)
        obj._assumptions._generator = tmp_asm_copy  # Issue #8873
        return obj

    __xnew__ = staticmethod(__new_stage2__)  # never cached (e.g. dummy)
    __xnew_cached_ = staticmethod(cacheit(__new_stage2__))  # symbols are always cached

    def __getnewargs__(self):
        return (self.name,)

    def __getstate__(self):
        return {'_assumptions': self._assumptions}

    def _hashable_content(self):
        # Note: user-specified assumptions not hashed, just derived ones
        hashable_content = [*self.assumptions_hashable().items()]
        hashable_content.sort()
        return (self.name,) + tuple(hashable_content)

    def _ask(self, fact):
        a = Expr._ask(self, fact)
        if a is True:
            self._assumptions[fact] = S.true
        elif a is False:
            self._assumptions[fact] = S.false
        return a

    def _eval_subs(self, old, new, **hints):
        from sympy.core.power import Pow
        if old.is_Pow:
            return Pow(self, S.One, evaluate=False)._eval_subs(old, new, **hints)

    @property
    def assumptions0(self):
        return {key: value for key, value in self._assumptions.items() if value is not None}

    def assumptions_hashable(self):
        return {k: v for k, v in self._assumptions.items() if v is not None and not isinstance(v, BooleanAtom)}

    @cacheit
    def sort_key(self, order=None):
        if self.domain_assumed:
            # to distinguish symbols with the same literals but different domains
            args = (self.name, True)
        else:
            args = (self.name,)
        return self.class_key(), (0, (), args), S.One.sort_key(), S.One

    def as_dummy(self):
        return Dummy(self.name)

    def as_real_imag(self, deep=True, **hints): 
        if hints.get('ignore') == self:
            return None
        
        from sympy import Im, Re
        return Re(self), Im(self)

    def is_constant(self, *wrt, **flags):
        if not wrt:
            return False
        return not self in wrt
    
    @cacheit
    def _eval_free_symbols(self):
        definition = self.definition
        if definition is None:
            return {self}
        
        free_symbols = definition.free_symbols
        if self.is_bounded:
            return free_symbols | {self}
        return free_symbols

    @property
    def binary_symbols(self):
        return self.free_symbols  # in this case, not always

    def as_set(self):
        return self.universalSet

    @property
    def is_unbounded(self):
        return not self.is_bounded
        
    def _eval_is_bounded(self):
        assumptions = self._assumptions
        for attr in ('domain', 'positive', 'negative', 'nonpositive', 'nonnegative', 'odd', 'even', 'prime'):
            if assumptions.get(attr) is not None:
                return True

    @property
    def is_bounded(self):
        if 'shape' in self._assumptions:
            return False
        return self._eval_is_bounded()

    @property
    def domain_assumed(self):        
        if domain := self._assumptions.get('domain'):
            return domain
        if distribution := self._assumptions.get('distribution'):
            return distribution.domain
        
    @property
    def domain_bounded(self):
        if domain := self._assumptions.get('domain'):
            return domain
        from sympy import Interval, oo, Range
        if self.is_positive:
            if self.is_integer:
                return Range(1, oo)
            return Interval(0, oo, left_open=True)
        if self.is_negative:
            if self.is_integer:
                return Range(-oo, 0)
            return Interval(-oo, 0, right_open=True)
        if self.is_nonpositive:
            if self.is_integer:
                return Range(-oo, 1)
            return Interval(-oo, 0)
        if self.is_nonnegative:
            if self.is_integer:
                return Range(oo)
            return Interval(0, oo)
        
    def domain_defined(self, x, **_):
        definition = self.definition
        if definition is None:
            return Expr.domain_defined(self, x)
        return definition.domain_defined(x)
        
    @property
    def domain(self):
        from sympy import Interval, Range, CartesianSpace

        if domain := self._assumptions.get('domain'):
            if self.is_integer and domain.is_Interval: 
                domain = domain.copy(integer=True)
            if self.shape:
                domain = CartesianSpace(domain, *self.shape)
            return domain
         
        if self.dtype.is_set:
            return self.universalSet
        
        if distribution := self._assumptions.get('distribution'):
            return distribution.domain
                         
        if self.is_extended_real:
            assumptions = self.assumptions0
            if 'integer' in assumptions:
                integer = assumptions.pop('integer')
            else:
                integer = self.is_integer

            if 'nonnegative' not in assumptions and self.is_nonnegative:
                assumptions['nonnegative'] = True
            elif 'positive' not in assumptions and self.is_positive:
                assumptions['positive'] = True

            if integer:
                domain = Range(**assumptions)
            else:
                domain = Interval(**assumptions)
        elif self.is_complex:
            domain = S.Complexes
        elif self.is_extended_complex:
            domain = S.ExtendedComplexes
        elif self.is_hyper_real:
            from sympy import HyperReals
            domain = HyperReals
        elif self.is_hyper_complex:
            from sympy import HyperComplexes
            domain = HyperComplexes
        elif self.is_super_real:
            from sympy import SuperReals
            domain = SuperReals
        else:
            from sympy import SuperComplexes
            domain = SuperComplexes
            
        shape = self.shape
        if not shape:
            return domain
        return CartesianSpace(domain, *shape)        

    @property
    def definition(self):
        if definition := self._assumptions.get('definition'):
            return definition

    @property
    def var(self):
        from sympy.stats.rv import pspace
        return pspace(self).symbol

    @property
    def surrogate(self):
        assert self.is_random
        from sympy.stats.symbolic_probability import Surrogate
        return Surrogate(self)

    def __and__(self, other):
        """Overloading for & operator"""
        if self.is_random and other.is_random:
            if not other.is_bool:
                other = other.as_boolean()
            return self.as_boolean() & other

        return super(Symbol, self).__and__(other)

    @cacheit
    def defun(self):
        if definition := self._assumptions.get('definition'):
            return definition
                
    def domain_nonzero(self, x):
        if self == x:
            return x.domain - {0}
        return Expr.domain_nonzero(self, x)

    @property
    def is_set(self):
        if self.shape:
            return False
        if etype := self._assumptions.get('etype'):
            return True
        definition = self.definition
        if definition is not None:
            return definition.is_set
        return False

    @property
    def dtype(self):
        definition = self.definition
        if definition is not None:
            return definition.dtype

        if etype := self._assumptions.get('etype'):
            return etype.set
        
        assumptions = {}
        if self._assumptions.get('positive'):
            assumptions['positive'] = True
        elif self._assumptions.get('nonnegative'):
            assumptions['nonnegative'] = True
        elif self._assumptions.get('negative'):
            assumptions['negative'] = True
        elif self._assumptions.get('nonpositive'):
            assumptions['nonpositive'] = True
        elif self._assumptions.get('bool'):
            return dtype.bool
             
        if self.is_super_integer:
            if self.is_integer:
                return dtype.integer(**assumptions)
            elif self.is_extended_integer:
                return dtype.extended_integer
            else:
                return dtype.super_integer
            
        elif self.is_super_rational:
            if self.is_rational:
                return dtype.rational
            elif self.is_extended_rational:
                return dtype.extended_rational
            elif self.is_hyper_rational:
                return dtype.hyper_rational
            else:
                return dtype.super_rational
            
        elif self.is_super_real:
            if self.is_real:
                return dtype.real
            elif self.is_extended_real:
                return dtype.extended_real
            elif self.is_hyper_real:
                return dtype.hyper_real
            else:
                return dtype.super_real

        else:
            if self.is_complex:
                return dtype.complex
            elif self.is_extended_complex:
                return dtype.extended_complex
            elif self.is_hyper_complex:
                return dtype.hyper_complex
            elif (domain := self._assumptions.get('domain')) and isinstance(domain, type):
                return domain.etype
            else:
                return dtype.super_complex
            
    @cacheit
    def _has(self, pattern):
        """Helper for .has()"""
        if Expr._has(self, pattern):
            return True

        if pattern.is_Sliced:
            if pattern.base == self:
                return True

        if not (isinstance(pattern, ManagedProperties) or pattern.is_FunctionClass):
            if definition := self._assumptions.get('definition'):
                return definition._has(pattern)

            if domain := self._assumptions.get('domain'):
                from sympy.core.numbers import Infinity, NegativeInfinity
                if isinstance(pattern, (Infinity, NegativeInfinity)):  # excludes oo, -oo, because these are not variables;
                    return False
                return domain._has(pattern)
        return False

    @property
    def etype(self):
        if etype := self._assumptions.get('etype'):
            return etype
        definition = self.definition
        if definition is not None:
            return definition.etype

    def element_symbol(self, excludes=set(), var=None):
        etype = self.etype
        if etype is None:
            return

        return self.generate_var(excludes=excludes, var=var, **etype.dict)

    def equality_defined(self):
        from sympy import Mul, Equal
        from sympy.concrete.expr_with_limits import Stack
        definition = self.definition
        if definition.is_Stack:
            vars = definition.variables[::-1]
            return Equal(self[vars], definition[vars], evaluate=False, plausible=None)
        elif definition.is_Mul:
            args = []
            ref = None
            for arg in definition.args:
                if isinstance(arg, Stack):
                    assert ref is None
                    ref = arg
                else:
                    args.append(arg)
            if ref is not None:
                (var, *_), *_ = ref.limits
                return Equal(self[var], Mul(*args) * ref.expr, evaluate=False, plausible=None)
        
        return Equal(self, self.definition, evaluate=False, plausible=None)
        
    @cacheit
    def _eval_shape(self):
        return self.get_shape()
    
    def get_shape(self):
        if 'shape' in self._assumptions:
            return self._assumptions['shape']
        
        if domain := self._assumptions.get('domain'):
            dtype = domain.etype
            shape = dtype.shape
        elif self.definition is not None:
            shape = self.definition.shape
        else:
            shape = ()
            
        return shape

    @property
    def cols(self):
        if self.shape:
            return self.shape[-1]
        return 1

    @property
    def rows(self):
        if len(self.shape) == 1:
            return 1
        if len(self.shape) > 1:
            return self.shape[-2]
        return 1

    def __iter__(self):
        raise TypeError

    def __setitem__(self, indices, value):
        from sympy import Indexed, Sliced
        if isinstance(indices, tuple):
            if isinstance(indices[-1], slice):
                
                value, *slices = value.of(Sliced)
                
                size = len(slices)
                for i in range(size):
                    start, stop = slices[i].of(Tuple)
                    index = indices[i - size]
                    _start = index.start
                    if _start is None:
                        _start = 0
                         
                    _stop = index.stop
                    if _stop is None:
                        _stop = value.shape[i]
                        
                    assert _start == start
                    assert _stop == stop
                    
                indices = indices[:-size]
                self[indices] = value
            else:
                args = value.of(Indexed)
                assert self == args[0]
                assert args[1:] == indices
        elif isinstance(indices, slice):
            value, sliced = value.of(Sliced)
            
            start, stop = sliced.of(Tuple)
            _start = indices.start
            if _start is None:
                _start = 0
                 
            _stop = indices.stop
            if _stop is None:
                _stop = value.shape[0]
                
            assert _start == start
            assert _stop == stop
        else:
            base, index = value.of(Indexed)
            assert self == base
            assert index == indices
        
    def __getitem__(self, indices, **kw_args):
        if (indices := self.simplify_indices(indices)) is None:
            return self
        
        from sympy.tensor.indexed import Indexed, Sliced, SlicedIndexed
        if isinstance(indices, tuple):
# Special case needed because M[*my_tuple] is a syntax error.
            if isinstance(indices[0], Tuple):
                for j in range(1, len(indices)):
                    if isinstance(indices[j], Tuple):
                        continue
                    
                    self = SlicedIndexed(self, *indices[:j], indices[j])
                    
                    indices = indices[j + 1:]
                    if indices:
                        self = self[indices]
                    return self
                else:
                    return Sliced(self, *indices)
            else:
                hit = False
                for j in range(1, len(indices)):
                    index = indices[j]
                    if isinstance(index, Tuple):
                        hit = True
                        break
                    
                if hit:
                    self = Indexed(self, *indices[:j])
                    indices = indices[j:]
                    if indices: 
                        self = self[indices]
                    return self
                return Indexed(self, *indices, **kw_args)
        elif isinstance(indices, Tuple):
            start, stop, step = indices.slice_args
            if start is None:
                start = 0
            if stop is None:
                stop = self.shape[0]
                
            if start == stop - 1:
                return Indexed(self, start, **kw_args)
            
            if start == 0 and stop == self.shape[0]:
                return self
            
            if step is None or step == 1:
                return Sliced(self, Tuple(start, stop), **kw_args)
            return Sliced(self, Tuple(start, stop, step), **kw_args)
        
        else:
            definition = self.definition
            if definition is not None and definition.is_Stack:
                if len(definition.limits) == 1 and definition.expr.is_RandomSymbol:
                    return definition[indices]

            boolean = indices < self.shape[0]
            assert boolean is True or boolean != False
            return Indexed(self, indices, **kw_args)
    
    #return exp._has(self)
    def has_match(self, exp):
        if exp == self:
            return True
        
        from sympy.matrices.expressions.matexpr import MatrixElement
        if isinstance(exp, MatrixElement) and exp.parent == self:
            return True
        
        if exp.is_Indexed and exp.base == self:
            return True
        if exp.is_Sliced:
            base = exp.base
            if base == self:
                for index in exp.indices:
                    if index.is_Tuple:
                        index_start, index_stop = index
                        start, stop = 0, self.shape[-1]
            
                        if index_stop <= start:
                            return False  # index < start
                        if index_start >= stop:
                            return False  # index >= stop
                # it is possible for them to be equal!
                        return True
                    else:
                        index_start, index_stop, index_step = index.args
                        start, stop = 0, self.shape[-1]
            
                        if index_stop <= start:
                            return False  # index < start
                        if index_start >= stop:
                            return False  # index >= stop
                # it is possible for them to be equal!
                        return True
            elif base.is_Indexed:
                base = base.base
                if base == self:
                    return True
                
        return False
    
    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            if len(self.shape) < 2:
                return self

    underscores = dict(_quote="'", _star='_*', _dquote='"')
    @classmethod
    def translate_underscore(cls, name):
        try:
            i = name.rindex('_')
            strUnderscore = name[i:]
            if strUnderscore := cls.underscores.get(strUnderscore):
                return name[:i] + strUnderscore
        except:
            ...

        return name
        
    @staticmethod
    def subs_specials(name):
        def subs(m):
            match m[0]:
                case '{':
                    return ''
                case '}':
                    return ''
                case '\\':
                    return ''
                case '#':
                    return 'sharp'
                case '.':
                    return '.'
                case _:
                    return '_'
        
        return re.sub('\\W', subs, name)

    def _sympystr(self, p):
        name = self.name
        if isinstance(name, str):
            sym = Symbol.subs_specials(self.name)
            if random_symbols := p._context.get('random_symbols'):
                if self in random_symbols:
                    sym += '.var' 
            return sym
        self, *attr = name
        return f'{self}.{".".join(attr)}'

    def _lean(self, p):
        name = self.name
        if isinstance(name, str):
            sym = Symbol.subs_specials(self.name)
            if random_symbols := p._context.get('random_symbols'):
                if self in random_symbols:
                    sym += '.var' 
            return sym
        self, *attr = name
        return f'{self}.{".".join(attr)}'

    def _latex(self, p, **kwargs):
        if self in p._settings['symbol_names']:
            return p._settings['symbol_names'][self]

        name = self.name
        if isinstance(name, str):
            name = Symbol.translate_underscore(name)
            result = p._deal_with_super_sub(name) if '\\' not in name else name

            if self.is_random:
                color = kwargs.get('color', 'red')
                return r'{\color{%s} {%s}}' % (color, result)
            
            if self.definition is not None:
                return r"{\color{blue} {%s}}" % result

            if self.is_given == False:
                return r"{\color{purple} {%s}}" % result
            
            if self.domain_assumed:
                return r"{\color{green} {%s}}" % result
            
            return result
        self, *attr = name
        return f'{self._latex(p)}.{".".join(attr)})'

    def _eval_is_extended_positive(self):
        if domain := self._assumptions.get('domain'):
            return domain.is_extended_positive
        if definition := self._assumptions.get('definition'):
            return definition.is_extended_positive
        if distribution := self._assumptions.get('distribution'):
            return distribution.is_extended_positive
        if etype := self._assumptions.get('etype'):
            return etype.is_extended_positive
                 
    def _eval_is_extended_negative(self):
        if domain := self._assumptions.get('domain'):
            return domain.is_extended_negative
        if definition := self._assumptions.get('definition'):
            return definition.is_extended_negative
        if distribution := self._assumptions.get('distribution'):
            return distribution.is_extended_negative
        if etype := self._assumptions.get('etype'):
            return etype.is_extended_negative

    def _eval_is_nonzero(self):
        if self.get_shape():
            return
            
        zero = self.is_zero
        if zero:
            return False
        
        if zero == False:
            return self.is_complex

    def _eval_is_zero(self):
        if domain := self._assumptions.get('domain'):
            return domain.is_zero
        if definition := self._assumptions.get('definition'):
            return definition.is_zero
        if distribution := self._assumptions.get('distribution'):
            return distribution.is_zero
        
    def _eval_is_finite(self):
        if domain := self._assumptions.get('domain'):
            if isinstance(domain, type):
                return
            if domain.is_Range or domain.is_Interval: 
                return True
            if domain.is_FiniteSet:
                if all(arg.is_finite for arg in domain.args):
                    return True
                if all(arg.is_infinite for arg in domain.args):
                    return False
            return
        
        definition = self._assumptions.get('definition')
        if definition is not None:
            return definition.is_finite
        
        for key in self._assumptions.keys() & {'integer', 'real', 'complex', 'rational', 'prime', 'even', 'odd', 'composite', 'irrational', 'finite'}:
            if self._assumptions[key]:
                return True

    def _eval_is_extended_integer(self):
        if domain := self._assumptions.get('domain'):
            return domain.is_extended_integer
        if definition := self._assumptions.get('definition'):
            return definition.is_extended_integer
        if distribution := self._assumptions.get('distribution'):
            return distribution.is_extended_integer
        if etype := self._assumptions.get('etype'):
            return etype.is_extended_integer

    def _eval_is_super_integer(self):
        if domain := self._assumptions.get('domain'):
            if isinstance(domain, type):
                return
            return domain.is_super_integer
        if definition := self._assumptions.get('definition'):
            return definition.is_super_integer
        if distribution := self._assumptions.get('distribution'):
            return distribution.is_super_integer
        if etype := self._assumptions.get('etype'):
            return etype.is_super_integer
        
    def _eval_is_extended_rational(self):
        if domain := self._assumptions.get('domain'):
            return domain.is_extended_rational
        if definition := self._assumptions.get('definition'):
            return definition.is_extended_rational
        if distribution := self._assumptions.get('distribution'):
            return distribution.is_extended_rational
        if etype := self._assumptions.get('etype'):
            return etype.is_extended_rational

    def _eval_is_hyper_rational(self):
        if domain := self._assumptions.get('domain'):
            return domain.is_hyper_rational
        if definition := self._assumptions.get('definition'):
            return definition.is_hyper_rational
        if distribution := self._assumptions.get('distribution'):
            return distribution.is_hyper_rational
        if etype := self._assumptions.get('etype'):
            return etype.is_hyper_rational

    def _eval_is_super_rational(self):
        if domain := self._assumptions.get('domain'):
            if isinstance(domain, type):
                return
            return domain.is_super_rational
        if definition := self._assumptions.get('definition'):
            return definition.is_super_rational
        if distribution := self._assumptions.get('distribution'):
            return distribution.is_super_rational
        if etype := self._assumptions.get('etype'):
            return etype.is_super_rational

    def _eval_is_extended_real(self):
        if domain := self._assumptions.get('domain'):
            return domain.is_extended_real
        if definition := self._assumptions.get('definition'):
            return definition.is_extended_real
        if distribution := self._assumptions.get('distribution'):
            return distribution.is_extended_real
        if etype := self._assumptions.get('etype'):
            return etype.is_extended_real

    def _eval_is_hyper_real(self):
        if domain := self._assumptions.get('domain'):
            return domain.is_hyper_real
        if definition := self._assumptions.get('definition'):
            return definition.is_hyper_real
        if distribution := self._assumptions.get('distribution'):
            return distribution.is_hyper_real
        if etype := self._assumptions.get('etype'):
            return etype.is_hyper_real
        
    def _eval_is_super_real(self):
        if domain := self._assumptions.get('domain'):
            if isinstance(domain, type):
                return
            return domain.is_super_real
        if definition := self._assumptions.get('definition'):
            return definition.is_super_real
        if distribution := self._assumptions.get('distribution'):
            return distribution.is_super_real
        if etype := self._assumptions.get('etype'):
            return etype.is_super_real

    def _eval_is_extended_complex(self):
        if domain := self._assumptions.get('domain'):
            if isinstance(domain, type):
                return
            return domain.is_extended_complex
        if definition := self._assumptions.get('definition'):
            return definition.is_extended_complex
        if distribution := self._assumptions.get('distribution'):
            return distribution.is_extended_complex
        if etype := self._assumptions.get('etype'):
            return etype.is_extended_complex

    def _eval_is_hyper_complex(self):
        if domain := self._assumptions.get('domain'):
            if isinstance(domain, type):
                return
            return domain.is_hyper_complex
        if definition := self._assumptions.get('definition'):
            return definition.is_hyper_complex
        if distribution := self._assumptions.get('distribution'):
            return distribution.is_hyper_complex
        if etype := self._assumptions.get('etype'):
            return etype.is_hyper_complex

    def _eval_is_algebraic(self):
        if domain := self._assumptions.get('domain'):
            return domain.is_algebraic
        if definition := self._assumptions.get('definition'):
            return definition.is_algebraic
    
    def _eval_is_hermitian(self):
        if domain := self._assumptions.get('domain'):
            return domain.is_hermitian
        if definition := self._assumptions.get('definition'):
            return definition.is_hermitian
    
    def _eval_is_imaginary(self):
        if domain := self._assumptions.get('domain'):
            return domain.is_imaginary
        if definition := self._assumptions.get('definition'):
            return definition.is_imaginary

    def _eval_is_random(self):
        if 'distribution' in self._assumptions:
            return True
        if definition := self._assumptions.get('definition'):
            return definition.is_random

    def _eval_is_even(self):
        if domain := self._assumptions.get('domain'):
            if domain.is_Range:
                if domain.step.is_even:
                    if domain.start.is_even:
                        return True
                    if domain.start.is_odd:
                        return False

    def _eval_is_odd(self):
        if domain := self._assumptions.get('domain'):
            if domain.is_Range:
                if domain.step.is_even:
                    if domain.start.is_odd:
                        return True
                    if domain.start.is_even:
                        return False

    @property
    def distribution(self):
        if distribution := self._assumptions.get('distribution'): 
            return distribution
    
#    given = True, for counter-proposition purposes;
#    given = False, for mathematical-induction purposes;
#    given = None, for others cases;
    @property
    def is_given(self):
        given = self._assumptions.get('given')
        if given is not None:
            return given
        definition = self.definition
        if definition is not None:
            return True
    
    def __hash__(self):
        return super(Symbol, self).__hash__()

    nonboolean_attributes = {'domain', 'shape', 'etype', 'distribution'}
    
    def __eq__(self, other):
        try:
            other = sympify(other)
            if type(other) != type(self):
                return False
        except:
            return False
        
        if self.name != other.name:
            return False
        
        definition = self.definition
        _definition = other.definition
        if definition != _definition:
            return False
        
        if definition is not None:
            return True
                
        for attr in Symbol.nonboolean_attributes:
            if (attr in self._assumptions) != (attr in other._assumptions):
                return False
        
        for fact in self._assumptions.keys() & other._assumptions.keys():
            if self._assumptions[fact] != other._assumptions[fact]:
                return False

        for fact in self._assumptions.keys() - other._assumptions.keys() - Symbol.nonboolean_attributes: 
            if other._ask(fact) != self._assumptions[fact]:
                return False
            
        for fact in other._assumptions.keys() - self._assumptions.keys() - Symbol.nonboolean_attributes:
            if self._ask(fact) != other._assumptions[fact]:
                return False

        return True
      
    def is_independent_of(self, y, **kwargs):
        from sympy.core.relational import Equal
        return Equal(self | y, self, **kwargs)

    def as_boolean(self, **kwargs):
        if self.is_random:            
            if kwargs.get('surrogate'):
                rhs = self.surrogate
            else:
                from sympy.stats.rv import pspace
                rhs = pspace(self).symbol

            from sympy import Equal
            return Equal(self, rhs)

    def _subs(self, old, new, **hints):
        """Substitutes an expression old -> new. when self is a Symbol
        """        
        assert old != new
        
        if old.is_Symbol:
            if self == old:
                return new
            if not old.shape and not old.is_set and hints.get('symbol') is not False:
                etype = self.etype
                if etype: 
                    _element_type = etype._subs(old, new)
                    if _element_type is not etype:
                        assumptions = self.assumptions_hashable()
                        assumptions['etype'] = _element_type
                        return self.func(r"{%s}_{%s}" % (self.name, str(new)), **assumptions)
                    
                definition = self.definition
                if definition is not None:
                    if definition.is_Stack:
                        for var in definition.variables:
                            if old == var:
                                return self
                            if old in var.free_symbols:
                                return self
                    _definition = definition._subs(old, new)
                    if _definition != definition:
                        assumptions = self.assumptions_hashable()
                        if 'shape' in assumptions:
                            del assumptions['shape']
        # rgb values for colors
        #                 https://www.917118.com/tool/color_3.html
        # darkyellow
                        assumptions.pop('definition')
                        return self.func(r"{\color{ADAD00} %s}" % self.name, _definition, **assumptions)
        return self
        
    def is_continuous_at(self, *args):
        definition = self.definition
        if definition is None:
            return True
        return definition.is_continuous_at(*args)
        
    def of(self, cls, **kwargs):
        from sympy import Set
        if cls is Set and self.is_set:
            return self

        if isinstance(cls, Symbol):
            if self != cls:
                return

        return AtomicExpr.of(self, cls)
    
    def of_simple_poly(self, x):
        '''
        extract the coefficients of a simple polynomial
        (a * x + b).of_simple_poly(x) = [b, a]
        '''
        if self == x:
            return S.Zero, S.One
        
        return AtomicExpr.of_simple_poly(self, x)
    
    def monotonicity(self, x):
        if self == x:
            return self, 1
        
        if (definition := self.definition) is not None and definition._has(x):
            return definition.monotonicity(x)
        return Expr.monotonicity(self, x)
    
    def min(self):
        if (definition := self.definition) is None:
            if self.is_set:
                from sympy import ReducedMin
                return ReducedMin(self)
            return self
        return definition.min()

    def max(self):
        if (definition := self.definition) is None:
            if self.is_set:
                from sympy import ReducedMax
                return ReducedMax(self)
            return self
        return definition.min()
    
    def invert(self):
        from sympy.logic.boolalg import Not
        return Not(self)

    @property
    def is_bool(self):
        return self._assumptions.get('bool')
    
    def __rshift__(self, other):
        """Overloading for >>"""
        return Imply(self, other)
    
    def __lshift__(self, other):
        """Overloading for <<"""
        return Given(self, other)
    
    def find_path(self, cls, path, **kwargs):
        for attr in kwargs:
            value = getattr(self, attr)
            if value is not None:
                path.append(attr)
                yield from value.find_path(cls, path, **kwargs)
                path.pop()
                
# performing other.indices in self.indices
    def index_contains(self, other):
        if other.is_Sliced:
            base = other.base
            if base.is_Indexed:
                base = other.base

            return self.index_contains(base)

        if other.is_Indexed:
            return other.base == self

        if other.is_SlicedIndexed:
            return other.base == self
        
        if other.is_Symbol:
            return self == other

# performing indices intersection
    def index_intersect(self, other):
        if other.is_Sliced:
            base = other.base
            if base.is_Indexed:
                base = other.base

            if self.index_contains(base):
                return other
            else:
                return

        if other.is_Indexed:
            if other.base == self:
                return other
            return

        if other.is_SlicedIndexed:
            if other.base == self:
                return other
            return
        
        if other.is_Symbol:
            if self == other:
                return other
            return

# performing indices complement
    def index_complement(self, other):
        if other.is_Sliced:
            base = other.base
            if base.is_Indexed:
                base = other.base
            else:
                if self == base:
                    (start, stop), *slices = other.indices
                    if stop.is_Infinity:
                        rest = {self[:start]}
                    elif start == 0:
                        rest = {self[stop:]}
                    else:
                        rest = {self[:start], self[stop:]}
                        
                    if slices:
                        rest |= self[start:stop].index_complement(other)
                    
                    if len(rest) == 1:
                        rest, = rest
                    return rest

            return self

        if other.is_Indexed:
            if other.base == self:
                b, index, *indices = other.args
                rest = {self[:index], self[index + 1:]}
                if indices:
                    rest |= self[index].index_complement(other)
                return rest
            
            return self

        if other.is_SlicedIndexed:
            if other.base == self:
                return
            return self
        
        if other.is_Symbol:
            if self == other:
                return
            return self

    def indexOf(self, indexed):
        if indexed.is_Indexed:
            if indexed.base == self:
                return indexed.indices
            
        if indexed.is_Sliced:
            if indexed.base == self:
                return indexed.indices

        if indexed.is_SlicedIndexed:
            if indexed.base == self:
                return indexed.indices

    def is_consistently_of(self, struct):
        return struct is not Symbol and struct.is_Symbol

    @classmethod
    def compare_hashable_content(cls, lhs, rhs):
        l, *st = lhs
        r, *ot = rhs
        if c := (len(st) > len(ot)) - (len(st) < len(ot)):
            return c

        if c := (l > r) - (l < r):
            return c

        for (name_left, l), (name_right, r) in zip(st, ot):
            if c := (name_left > name_right) - (name_left < name_right):
                return c
                
            if isinstance(l, (Basic, Dtype)):
                c = l.compare(r)
            else:
                c = (l > r) - (l < r)
            if c:
                return c
        return 0
        
    def compare(self, other):
        # all redefinitions of __cmp__ method should start with the following lines:
        if self.__class__ != other.__class__:
            return AtomicExpr.compare(self, other)
        return Symbol.compare_hashable_content(self._hashable_content(), other._hashable_content())

    @classmethod
    def compile_definition_statement(cls, line):
        if m := re.match(r'(.+?) *= *(Symbol|Function)\((.+)\) *$', line):
            name, func, kwargs = m.groups()
            if ',' in name:
                line = "%s = %s" % (name, ', '.join(["%s('%s', %s)" % (func, n, kwargs) for n in re.split(r"\s*,\s*", name)]))
            elif re.match("'[^']+'", kwargs) or re.match('"[^"]+"', kwargs):
                ...
            else:
                line = "%s = %s('%s', %s)" % (name, func, name, kwargs)
                
        return line

    @classmethod
    def definition_append(cls, definition, next_definitions):
        for next_sym, next_definition in next_definitions:
            for i in range(len(definition) - 1, -1, -1):
                last_sym, last_definition = definition[i]
                if (m_last := re.search(fr'(.+) = (Symbol|Function)\((.+)\)', last_definition)):
                    if (m_next := re.search(fr'(.+) = (Symbol|Function)\((.+)\)', next_definition)) and m_last[2] == m_next[2] and m_last[3] == m_next[3]:
                        if isinstance(last_sym, list):
                            if isinstance(next_sym, list):
                                last_sym += next_sym
                            else: 
                                last_sym.append(next_sym)
                        else:
                            if isinstance(next_sym, list):
                                last_sym = [last_sym, *next_sym]
                            else: 
                                last_sym = [last_sym, next_sym]

                        definition[i] = last_sym, f'{m_last[1]}, {m_next[1]} = {m_last[2]}({m_last[3]})'
                        break
                
                    def definition_delete(next_sym):
                        if next_sym.is_random == True:
                            if isinstance(last_sym, list):
                                try:
                                    index = last_sym.index(next_sym.var)
                                    del last_sym[index]
                                    vars = m_last[1].split(", ")
                                    del vars[index]
                                    if len(last_sym) == 1:
                                        last, = last_sym
                                    else:
                                        last = last_sym
                                    definition[i] = last, f"{', '.join(vars)} = {m_last[2]}({m_last[3]})" 
                                except:
                                    ...
                            elif next_sym.var == last_sym:
                                del definition[i]
                
                    if isinstance(next_sym, list):
                        for next_sym in next_sym:
                            definition_delete(next_sym)
                    else:
                        definition_delete(next_sym)
            else:
                definition.append((next_sym, next_definition))
        return definition
        
    def python_definition(self, free_symbols, random_symbols):
        definition = []
        if self not in free_symbols | random_symbols:
            kwargs = []
            if domain := self._assumptions.get('domain'):
                Symbol.definition_append(definition, domain.python_definition(free_symbols, random_symbols))
                kwargs.append(f'domain={domain}')
                if shape := self.shape:
                    for e in shape:
                        if isinstance(e, Basic):
                            Symbol.definition_append(definition, e.python_definition(free_symbols, random_symbols))
                    
                    kwargs.append(f'shape={shape}')
            else:
                for k, v in self.type.dict.items():
                    if isinstance(v, Basic):
                        Symbol.definition_append(definition, v.python_definition(free_symbols, random_symbols))
                    elif isinstance(v, tuple):
                        for e in v:
                            if isinstance(e, Basic):
                                Symbol.definition_append(definition, e.python_definition(free_symbols, random_symbols))
                    elif isinstance(v, Dtype):
                        Symbol.definition_append(definition, v.python_definition(free_symbols, random_symbols))
                        v = f"dtype.{v}"
        
                    kwargs.append(f"{k}={v}")
                
            if self.is_even:
                kwargs.append("even=True")
                
            if self.is_odd:
                kwargs.append("odd=True")
                
            if self.is_random:
                kwargs.append("random=True")
                free_symbols.add(self.var)
                random_symbols.add(self)
            else:
                free_symbols.add(self)
    
            kwargs = ', '.join(kwargs)
            
            sym = str(self)
            if re.search('\\W', self.name):
                name = self.name.replace('"', '\\"')
                if '\\' in self.name:
                    kwargs = f'r"{name}", {kwargs}'
                else:
                    kwargs = f'"{name}", {kwargs}'
            Symbol.definition_append(definition, [(self, f'{sym} = Symbol({kwargs})')])
        return definition

    def _eval_try_div(self, factor):
        if factor.is_Mul:
            try:
                index = factor.args.index(self)
                [*args] = factor.args
                del args[index]
                return factor.func(*args)
            except IndexError:
                ...


class Dummy(Symbol):
    """Dummy symbols are each unique, even if they have the same name:

    >>> from sympy import Dummy
    >>> Dummy("x") == Dummy("x")
    False

    If a name is not supplied then a string value of an internal count will be
    used. This is useful when a temporary variable is needed and the name
    of the variable used in the expression is not important.

    >>> Dummy() #doctest: +SKIP
    _Dummy_10

    """

    # In the rare event that a Dummy object needs to be recreated, both the
    # `name` and `dummy_index` should be passed.  This is used by `srepr` for
    # example:
    # >>> d1 = Dummy()
    # >>> d2 = eval(srepr(d1))
    # >>> d2 == d1
    # True
    #
    # If a new session is started between `srepr` and `eval`, there is a very
    # small chance that `d2` will be equal to a previously-created Dummy.

    _count = 0
    _prng = random.Random()
    _base_dummy_index = _prng.randint(10 ** 6, 9 * 10 ** 6)

    __slots__ = ['dummy_index']

    def __new__(cls, name=None, dummy_index=None, **assumptions):
        if dummy_index is not None:
            assert name is not None, "If you specify a dummy_index, you must also provide a name"

        if name is None:
            name = "Dummy_" + str(Dummy._count)

        if dummy_index is None:
            dummy_index = Dummy._base_dummy_index + Dummy._count
            Dummy._count += 1

        cls._sanitize(assumptions, cls)
        obj = Symbol.__xnew__(cls, name, **assumptions)

        obj.dummy_index = dummy_index

        return obj

    def __getstate__(self):
        return {'_assumptions': self._assumptions, 'dummy_index': self.dummy_index}

    @cacheit
    def sort_key(self, order=None):
        return self.class_key(), (0, (), (self.name, self.dummy_index)), S.One.sort_key(), S.One

    def _hashable_content(self):
        return Symbol._hashable_content(self) + (self.dummy_index,)

    def compare(self, other):
        if self.__class__ != other.__class__:
            return AtomicExpr.compare(self, other)

        *st, l_int = self._hashable_content()
        *ot, r_int = other._hashable_content()
        
        if c := Symbol.compare_hashable_content(st, ot):
            return c

        return l_int - r_int


class Wild(Symbol):
    """
    A Wild symbol matches anything, or anything
    without whatever is explicitly excluded.

    Parameters
    ==========

    name : str
        Name of the Wild instance.
    exclude : iterable, optional
        Instances in ``exclude`` will not be matched.
    properties : iterable of functions, optional
        Functions, each taking an expressions as input
        and returns a ``bool``. All functions in ``properties``
        need to return ``True`` in order for the Wild instance
        to match the expression.

    Examples
    ========

    >>> from sympy import Wild, WildFunction, cos, pi
    >>> from sympy.abc import x, y, z
    >>> a = Wild('a')
    >>> x.match(a)
    {a_: x}
    >>> pi.match(a)
    {a_: pi}
    >>> (3*x**2).match(a*x)
    {a_: 3*x}
    >>> cos(x).match(a)
    {a_: cos(x)}
    >>> b = Wild('b', exclude=[x])
    >>> (3*x**2).match(b*x)
    >>> b.match(a)
    {a_: b_}
    >>> A = WildFunction('A')
    >>> A.match(a)
    {a_: A_}

    Tips
    ====

    When using Wild, be sure to use the exclude
    keyword to make the pattern more precise.
    Without the exclude pattern, you may get matches
    that are technically correct, but not what you
    wanted. For example, using the above without
    exclude:

    >>> from sympy import symbols
    >>> a, b = symbols('a b', cls=Wild)
    >>> (2 + 3*y).match(a*x + b*y)
    {a_: 2/x, b_: 3}

    This is technically correct, because
    (2/x)*x + 3*y == 2 + 3*y, but you probably
    wanted it to not match at all. The issue is that
    you really didn't want a and b to include x and y,
    and the exclude parameter lets you specify exactly
    this.  With the exclude parameter, the pattern will
    not match.

    >>> a = Wild('a', exclude=[x, y])
    >>> b = Wild('b', exclude=[x, y])
    >>> (2 + 3*y).match(a*x + b*y)

    Exclude also helps remove ambiguity from matches.

    >>> E = 2*x**3*y*z
    >>> a, b = symbols('a b', cls=Wild)
    >>> E.match(a*b)
    {a_: 2*y*z, b_: x**3}
    >>> a = Wild('a', exclude=[x, y])
    >>> E.match(a*b)
    {a_: z, b_: 2*x**3*y}
    >>> a = Wild('a', exclude=[x, y, z])
    >>> E.match(a*b)
    {a_: 2, b_: x**3*y*z}

    Wild also accepts a ``properties`` parameter:

    >>> a = Wild('a', properties=[lambda k: k.is_Integer])
    >>> E.match(a*b)
    {a_: 2, b_: x**3*y*z}

    """

    __slots__ = ['exclude', 'properties']

    def __new__(cls, name, exclude=(), properties=(), **assumptions):
        exclude = tuple([sympify(x) for x in exclude])
        properties = tuple(properties)
        cls._sanitize(assumptions, cls)
        return Wild.__xnew__(cls, name, exclude, properties, **assumptions)

    def __getnewargs__(self):
        return self.name, self.exclude, self.properties

    @staticmethod
    @cacheit
    def __xnew__(cls, name, exclude, properties, **assumptions):
        obj = Symbol.__xnew__(cls, name, **assumptions)
        obj.exclude = exclude
        obj.properties = properties
        return obj

    def _hashable_content(self):
        return super(Wild, self)._hashable_content() + (self.exclude, self.properties)

    # TODO add check against another Wild
    def matches(self, expr, repl_dict={}, old=False):
        if any(expr.has(x) for x in self.exclude):
            return None
        if any(not f(expr) for f in self.properties):
            return None
        repl_dict = repl_dict.copy()
        repl_dict[self] = expr
        return repl_dict

    @cacheit
    def _eval_shape(self):
        if 'shape' in self._assumptions:
            return self._assumptions['shape']
        return ()

    def compare(self, other):
        if self.__class__ != other.__class__:
            return AtomicExpr.compare(self, other)

        *st, lhs_exclude, lhs_properties = self._hashable_content()
        *ot, rhs_exclude, rhs_properties = other._hashable_content()
        
        if c := Symbol.compare_hashable_content(st, ot):
            return c

        if c := (len(lhs_exclude) > len(rhs_exclude)) - (len(lhs_exclude) < len(rhs_exclude)):
            return c

        if c := (len(lhs_properties) > len(rhs_properties)) - (len(lhs_properties) < len(rhs_properties)):
            return c
        
        return 0

_range = re.compile('([0-9]*:[0-9]+|[a-zA-Z]?:[a-zA-Z])')


def symbols(names, **args):
    r"""
    Transform strings into instances of :class:`Symbol` class.

    :func:`symbols` function returns a sequence of symbols with names taken
    from ``names`` argument, which can be a comma or whitespace delimited
    string, or a sequence of strings::

        >>> from sympy import symbols, Function

        >>> x, y, z = symbols('x,y,z')
        >>> a, b, c = symbols('a b c')

    The type of output is dependent on the properties of input arguments::

        >>> symbols('x')
        x
        >>> symbols('x,')
        (x,)
        >>> symbols('x,y')
        (x, y)
        >>> symbols(('a', 'b', 'c'))
        (a, b, c)
        >>> symbols(['a', 'b', 'c'])
        [a, b, c]
        >>> symbols({'a', 'b', 'c'})
        {a, b, c}

    If an iterable container is needed for a single symbol, set the ``seq``
    argument to ``True`` or terminate the symbol name with a comma::

        >>> symbols('x', seq=True)
        (x,)

    To reduce typing, range syntax is supported to create indexed symbols.
    Ranges are indicated by a colon and the type of range is determined by
    the character to the right of the colon. If the character is a digit
    then all contiguous digits to the left are taken as the nonnegative
    starting value (or 0 if there is no digit left of the colon) and all
    contiguous digits to the right are taken as 1 greater than the ending
    value::

        >>> symbols('x:10')
        (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9)

        >>> symbols('x5:10')
        (x5, x6, x7, x8, x9)
        >>> symbols('x5(:2)')
        (x50, x51)

        >>> symbols('x5:10,y:5')
        (x5, x6, x7, x8, x9, y0, y1, y2, y3, y4)

        >>> symbols(('x5:10', 'y:5'))
        ((x5, x6, x7, x8, x9), (y0, y1, y2, y3, y4))

    If the character to the right of the colon is a letter, then the single
    letter to the left (or 'a' if there is none) is taken as the start
    and all characters in the lexicographic range *through* the letter to
    the right are used as the range::

        >>> symbols('x:z')
        (x, y, z)
        >>> symbols('x:c')  # null range
        ()
        >>> symbols('x(:c)')
        (xa, xb, xc)

        >>> symbols(':c')
        (a, b, c)

        >>> symbols('a:d, x:z')
        (a, b, c, d, x, y, z)

        >>> symbols(('a:d', 'x:z'))
        ((a, b, c, d), (x, y, z))

    Multiple ranges are supported; contiguous numerical ranges should be
    separated by parentheses to disambiguate the ending number of one
    range from the starting number of the next::

        >>> symbols('x:2(1:3)')
        (x01, x02, x11, x12)
        >>> symbols(':3:2')  # parsing is from left to right
        (00, 01, 10, 11, 20, 21)

    Only one pair of parentheses surrounding ranges are removed, so to
    include parentheses around ranges, double them. And to include spaces,
    commas, or colons, escape them with a backslash::

        >>> symbols('x((a:b))')
        (x(a), x(b))
        >>> symbols(r'x(:1\,:2)')  # or r'x((:1)\,(:2))'
        (x(0,0), x(0,1))

    All newly created symbols have assumptions set according to ``args``::

        >>> a = symbols('a', integer=True)
        >>> a.is_integer
        True

        >>> x, y, z = symbols('x,y,z', real=True)
        >>> x.is_real and y.is_real and z.is_real
        True

    Despite its name, :func:`symbols` can create symbol-like objects like
    instances of Function or Wild classes. To achieve this, set ``cls``
    keyword argument to the desired type::

        >>> symbols('f,g,h', cls=Function)
        (f, g, h)

        >>> type(_[0])
        <class 'sympy.core.function.UndefinedFunction'>

    """
    result = []

    if isinstance(names, str):
        marker = 0
        literals = [r'\,', r'\:', r'\ ']
        for i in range(len(literals)):
            lit = literals.pop(0)
            if lit in names:
                while chr(marker) in names:
                    marker += 1
                lit_char = chr(marker)
                marker += 1
                names = names.replace(lit, lit_char)
                literals.append((lit_char, lit[1:]))

        def literal(s):
            if literals:
                for c, l in literals:
                    s = s.replace(c, l)
            return s

        names = names.strip()
        as_seq = names.endswith(',')
        if as_seq:
            names = names[:-1].rstrip()
        if not names:
            raise ValueError('no symbols given')

        # split on commas
        names = [n.strip() for n in names.split(',')]
        if not all(n for n in names):
            raise ValueError('missing symbol between commas')
        # split on spaces
        for i in range(len(names) - 1, -1, -1):
            names[i: i + 1] = names[i].split()

        cls = args.pop('cls', Symbol)
        seq = args.pop('seq', as_seq)

        for name in names:
            if not name:
                raise ValueError('missing symbol')

            if ':' not in name:
                symbol = cls(literal(name), **args)
                result.append(symbol)
                continue

            split = _range.split(name)
            # remove 1 layer of bounding parentheses around ranges
            for i in range(len(split) - 1):
                if i and ':' in split[i] and split[i] != ':' and \
                        split[i - 1].endswith('(') and \
                        split[i + 1].startswith(')'):
                    split[i - 1] = split[i - 1][:-1]
                    split[i + 1] = split[i + 1][1:]
            for i, s in enumerate(split):
                if ':' in s:
                    if s[-1].endswith(':'):
                        raise ValueError('missing end range')
                    a, b = s.split(':')
                    if b[-1] in string.digits:
                        a = 0 if not a else int(a)
                        b = int(b)
                        split[i] = [str(c) for c in range(a, b)]
                    else:
                        a = a or 'a'
                        split[i] = [string.ascii_letters[c] for c in range(
                            string.ascii_letters.index(a),
                            string.ascii_letters.index(b) + 1)]  # inclusive
                    if not split[i]:
                        break
                else:
                    split[i] = [s]
            else:
                seq = True
                if len(split) == 1:
                    names = split[0]
                else:
                    names = [''.join(s) for s in cartes(*split)]
                if literals:
                    result.extend([cls(literal(s), **args) for s in names])
                else:
                    result.extend([cls(s, **args) for s in names])

        if not seq and len(result) <= 1:
            if not result:
                return ()
            return result[0]

        return tuple(result)
    else:
        for name in names:
            result.append(symbols(name, **args))

        return type(names)(result)


def var(names, **args):
    """
    Create symbols and inject them into the global namespace.

    This calls :func:`symbols` with the same arguments and puts the results
    into the *global* namespace. It's recommended not to use :func:`var` in
    library code, where :func:`symbols` has to be used::

    Examples
    ========

    >>> from sympy import Symbol

    >>> var('x')
    x
    >>> x
    x

    >>> var('a,ab,abc')
    (a, ab, abc)
    >>> abc
    abc

    >>> var('x,y', real=True)
    (x, y)
    >>> x.is_real and y.is_real
    True

    See :func:`symbol` documentation for more details on what kinds of
    arguments can be passed to :func:`var`.

    """

    def traverse(symbols, frame):
        """Recursively inject symbols to the global namespace. """
        for symbol in symbols:
            if isinstance(symbol, Basic):
                frame.f_globals[symbol.name] = symbol
            elif symbol.is_FunctionClass:
                frame.f_globals[symbol.__name__] = symbol
            else:
                traverse(symbol, frame)

    from inspect import currentframe
    frame = currentframe().f_back

    try:
        syms = symbols(names, **args)

        if syms is not None:
            if isinstance(syms, Basic):
                frame.f_globals[syms.name] = syms
            elif syms.is_FunctionClass:
                frame.f_globals[syms.__name__] = syms
            else:
                traverse(syms, frame)
    finally:
        del frame  # break cyclic dependencies as stated in inspect docs

    return syms


def disambiguate(*iter):
    """
    Return a Tuple containing the passed expressions with symbols
    that appear the same when printed replaced with numerically
    subscripted symbols, and all Dummy symbols replaced with Symbols.

    Parameters
    ==========

    iter: list of symbols or expressions.

    Examples
    ========

    >>> from sympy.core.symbol import disambiguate
    >>> from sympy import Dummy, Symbol, Tuple
    >>> from sympy.abc import y

    >>> tup = Symbol('_x'), Dummy('x'), Dummy('x')
    >>> disambiguate(*tup)
    (x_2, x, x_1)

    >>> eqs = Tuple(Symbol('x')/y, Dummy('x')/y)
    >>> disambiguate(*eqs)
    (x_1/y, x/y)

    >>> ix = Symbol('x', integer=True)
    >>> vx = Symbol('x')
    >>> disambiguate(vx + ix)
    (x + x_1,)

    To make your own mapping of symbols to use, pass only the free symbols
    of the expressions and create a dictionary:

    >>> free = eqs.free_symbols
    >>> mapping = dict(zip(free, disambiguate(*free)))
    >>> eqs.xreplace(mapping)
    (x_1/y, x/y)

    """
    new_iter = Tuple(*iter)
    key = lambda x:tuple(sorted(x.assumptions0.items()))
    syms = ordered(new_iter.free_symbols, keys=key)
    mapping = {}
    for s in syms:
        mapping.setdefault(str(s).lstrip('_'), []).append(s)
    reps = {}
    for k in mapping:
        # the first or only symbol doesn't get subscripted but make
        # sure that it's a Symbol, not a Dummy
        mapk0 = Symbol("%s" % (k), **mapping[k][0].assumptions0)
        if mapping[k][0] != mapk0:
            reps[mapping[k][0]] = mapk0
        # the others get subscripts (and are made into Symbols)
        skip = 0
        for i in range(1, len(mapping[k])):
            while True:
                name = "%s_%i" % (k, i + skip)
                if name not in mapping:
                    break
                skip += 1
            ki = mapping[k][i]
            reps[ki] = Symbol(name, **ki.assumptions0)
    return new_iter.xreplace(reps)


class Dtype:

    is_tuple = False  # indicate a tuple of different data types
    is_bool = False
    is_set = False
    
    is_finite = None
    
    is_integer = None
    is_extended_integer = None
    is_super_integer = None
    
    is_rational = None
    is_extended_rational = None
    is_hyper_rational = None
    is_super_rational = None
    
    is_real = None
    is_extended_positive = None
    is_extended_negative = None
    is_extended_real = None
    is_hyper_real = None
    is_super_real = None
    
    is_complex = True
    is_extended_complex = None
    is_hyper_complex = None
    is_super_complex = True
    
    is_DtypeInteger = None
    
    def as_Set(self):
        from sympy.sets.sets import UniversalSet
        return UniversalSet(etype=self)
        
    def __hash__(self):
        return hash(type(self).__name__)

    @property
    def integer(self):
        return DtypeInteger()

    @property
    def natural(self):
        return self.integer(nonnegative=True)

    @property
    def extended_integer(self):
        return DtypeExtendedInteger()

    @property
    def super_integer(self):
        return DtypeSuperInteger()
    
    @property
    def rational(self):
        return DtypeRational()

    @property
    def extended_rational(self):
        return DtypeExtendedRational()
    
    @property
    def hyper_rational(self):
        return DtypeHyperRational()
    
    @property
    def super_rational(self):
        return DtypeSuperRational()
    
    @property
    def real(self):
        return DtypeReal()

    @property
    def extended_real(self):
        return DtypeExtendedReal()
    
    @property
    def hyper_real(self):
        return DtypeHyperReal()
    
    @property
    def super_real(self):
        return DtypeSuperReal()
    
    @property
    def complex(self):
        return DtypeComplex()

    @property
    def extended_complex(self):
        return DtypeExtendedComplex()

    @property
    def hyper_complex(self):
        return DtypeHyperComplex()
    
    @property
    def super_complex(self):
        return DtypeSuperComplex()
    
    @property
    def set(self):
        return DtypeSet(self)

    @property
    def bool(self):
        return DtypeBoolean()

    @property
    def distribution(self):
        return DtypeDistribution()

    def type(self, type):
        return DtypeType(type)

    @property
    def emptySet(self):
        from sympy import EmptySet
        return EmptySet(etype=self)
    
    @property
    def universalSet(self):
        from sympy.sets.sets import Set, UniversalSet
        return Set.__new__(UniversalSet, etype=self)

    def __getitem__(self, length):
        if isinstance(length, (tuple, Tuple, list)):
            if not length:
                return self
            return DtypeMatrix(self, tuple(length))
        return DtypeMatrix(self, (length,))

    def __contains__(self, other):
        return isinstance(other, type(self))

    @property
    def shape(self):
        return ()

    def _has(self, pattern):
        return False

    def _subs(self, old, new, **hints):
        return self
    
    def __repr__(self):
        return str(self)
    
    def __str__(self, head):
        return '%s(%s)' % (head, ', '.join(("%s=%s" % args for args in self.assumptions.items())))

    def compare(self, other):
        lhs = self.__class__
        rhs = other.__class__
        if lhs != rhs:
            lhs = str(lhs)
            rhs = str(rhs)
            return (lhs > rhs) - (lhs < rhs)
        
        [*lhs] = self.dict.items()
        [*rhs] = other.dict.items()
        
        if c := len(lhs) - len(rhs):
            return c 
        
        lhs.sort(key=lambda args: args[0])
        rhs.sort(key=lambda args: args[0])
        for (key_lhs, lhs), (key_rhs, rhs) in zip(lhs, rhs):
            if c := (key_lhs > key_rhs) - (key_lhs < key_rhs):
                return c
            
            if isinstance(lhs, (Basic, Dtype)):
                c = lhs.compare(rhs)
            else:
                c = (lhs > rhs) - (lhs < rhs)
                
            if c:
                return c
            
        return 0

    def python_definition(self, free_symbols, random_symbols):
        return []


class DtypeSuperComplex(Dtype):
    
    is_super_complex = True

    def as_Set(self):
        from sympy import SuperComplexes
        return SuperComplexes

    def __str__(self):
        return 'super_complex'
    
    @property
    def dict(self):
        return {'super_complex': True}

    def __eq__(self, other):
        return isinstance(other, DtypeSuperComplex)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeSuperComplexConditional(**kwargs)

    @property
    def universalSet(self):
        from sympy.sets.sets import Set, UniversalSet
        return Set.__new__(UniversalSet, etype=self.super_complex)
    
    def extended_type(self):
        return self


class DtypeSuperReal(DtypeSuperComplex):
    
    is_super_real = True
    
    @property
    def universalSet(self):
        from sympy.sets.sets import Set, UniversalSet
        return Set.__new__(UniversalSet, etype=self.super_real)
    
    def as_Set(self):
        from sympy import SuperReals
        return SuperReals

    def __str__(self):
        return 'super_real'
    
    @property
    def dict(self):
        return {'super_real': True}

    def __eq__(self, other):
        return isinstance(other, DtypeSuperReal)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeSuperRealConditional(**kwargs)
    

class DtypeSuperRational(DtypeSuperReal):
    
    is_super_rational = True
    
    @property
    def universalSet(self):
        from sympy.sets.sets import Set, UniversalSet
        return Set.__new__(UniversalSet, etype=self.super_rational)
    
    def as_Set(self):
        from sympy import SuperRationals
        return SuperRationals

    def __str__(self):
        return 'super_rational'
    
    @property
    def dict(self):
        return {'super_rational': True}

    def __eq__(self, other):
        return isinstance(other, DtypeSuperRational)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeSuperRationalConditional(**kwargs)
    

class DtypeSuperInteger(DtypeSuperRational):
    
    is_super_integer = True
    
    @property
    def universalSet(self):
        from sympy.sets.sets import Set, UniversalSet
        return Set.__new__(UniversalSet, etype=self.super_integer)
    
    def as_Set(self):
        from sympy import SuperIntegers
        return SuperIntegers

    def __str__(self):
        return 'super_integer'
    
    @property
    def dict(self):
        return {'super_integer': True}

    def __eq__(self, other):
        return isinstance(other, DtypeSuperInteger)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeSuperIntegerConditional(**kwargs)


class DtypeHyperComplex(DtypeSuperComplex):
    
    is_hyper_complex = True

    def as_Set(self):
        from sympy import HyperComplexes
        return HyperComplexes

    def __str__(self):
        return 'hyper_complex'
    
    @property
    def dict(self):
        return {'hyper_complex': True}

    def __eq__(self, other):
        return isinstance(other, DtypeHyperComplex)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeHyperComplexConditional(**kwargs)

    @property
    def universalSet(self): 
        from sympy.sets.sets import Set, UniversalSet
        return Set.__new__(UniversalSet, etype=self.hyper_complex)


class DtypeHyperReal(DtypeSuperReal, DtypeHyperComplex):
    
    is_hyper_real = True
    
    @property
    def universalSet(self):
        from sympy.sets.sets import Set, UniversalSet
        return Set.__new__(UniversalSet, etype=dtype.hyper_real)
    
    def as_Set(self):
        from sympy import HyperReals
        return HyperReals

    def __str__(self):
        return 'hyper_real'
    
    @property
    def dict(self):
        return {'hyper_real': True}

    def __eq__(self, other):
        return isinstance(other, DtypeHyperReal)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeHyperRealConditional(**kwargs)


class DtypeHyperRational(DtypeSuperRational, DtypeHyperReal):
    
    is_hyper_rational = True
    
    @property
    def universalSet(self):
        from sympy.sets.sets import Set, UniversalSet
        return Set.__new__(UniversalSet, etype=dtype.hyper_rational)
    
    def as_Set(self):
        from sympy import HyperRationals
        return HyperRationals

    def __str__(self):
        return 'hyper_rational'
    
    @property
    def dict(self):
        return {'hyper_rational': True}

    def __eq__(self, other):
        return isinstance(other, DtypeHyperRational)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeHyperRationalConditional(**kwargs)


class DtypeExtendedComplex(DtypeHyperComplex):
    
    is_extended_complex = True

    def as_Set(self):
        from sympy import ComplexRegion, oo, Interval
        ExtendedReals = Interval(-oo, oo, left_open=False, right_open=False)
        return ComplexRegion(ExtendedReals @ ExtendedReals)

    def __str__(self):
        return 'extended_complex'
    
    @property
    def dict(self):
        return {'extended_complex': True}

    def __eq__(self, other):
        return isinstance(other, DtypeExtendedComplex)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeExtendedComplexConditional(**kwargs)

    @property
    def universalSet(self): 
        from sympy import ComplexRegion, oo, Interval
        ExtendedReals = Interval(-oo, oo, left_open=False, right_open=False)
        return ComplexRegion(ExtendedReals @ ExtendedReals)


class DtypeExtendedReal(DtypeHyperReal, DtypeExtendedComplex):
    
    is_extended_real = True
    
    @property
    def universalSet(self):
        from sympy import Interval, oo
        return Interval(-oo, oo, left_open=False, right_open=False)
    
    def as_Set(self):
        from sympy import Interval, oo
        return Interval(-oo, oo, left_open=False, right_open=False)

    def __str__(self):
        return 'extended_real'
    
    @property
    def dict(self):
        return {'extended_real': True}

    def __eq__(self, other):
        return isinstance(other, DtypeExtendedReal)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeExtendedRealConditional(**kwargs)


class DtypeExtendedRational(DtypeHyperRational, DtypeExtendedReal):
    
    is_extended_rational = True
    
    @property
    def universalSet(self):
        from sympy import Interval, oo
        return Interval(-oo, oo, left_open=False, right_open=False, rational=True)
    
    def as_Set(self):
        from sympy import Interval, oo
        return Interval(-oo, oo, left_open=False, right_open=False, rational=True)

    def __str__(self):
        return 'extended_rational'
    
    @property
    def dict(self):
        return {'extended_rational': True}

    def __eq__(self, other):
        return isinstance(other, DtypeExtendedRational)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeExtendedRationalConditional(**kwargs)


class DtypeExtendedInteger(DtypeSuperInteger, DtypeExtendedRational):
    
    is_extended_integer = True
    
    @property
    def universalSet(self):
        from sympy import Range, oo
        return Range(-oo, oo, left_open=False, right_open=False)
    
    def as_Set(self):
        from sympy import Range, oo
        return Range(-oo, oo, left_open=False, right_open=False)

    def __str__(self):
        return 'extended_integer'
    
    @property
    def dict(self):
        return {'extended_integer': True}

    def __eq__(self, other):
        return isinstance(other, DtypeExtendedInteger)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeExtendedIntegerConditional(**kwargs)


class DtypeComplex(DtypeExtendedComplex):
    
    is_complex = True
    is_finite = True

    def as_Set(self):
        return S.Complexes

    def __str__(self):
        return 'complex'
    
    @property
    def dict(self):
        return {'complex': True}

    def __eq__(self, other):
        return isinstance(other, DtypeComplex)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeComplexConditional(**kwargs)

    @property
    def universalSet(self): 
        return S.Complexes

    def extended_type(self):
        return self.extended_complex


class DtypeComplexConditional(DtypeComplex):
    
    def as_Set(self):
        return S.Complexes

    def __init__(self, **assumptions):
        self.assumptions = assumptions
    
    def __str__(self):
        return Dtype.__str__(self, 'complex')
    
    @property
    def dict(self):
        assumptions = {**self.assumptions}
        assumptions['complex'] = True
        return assumptions

    def __eq__(self, other):
        return isinstance(other, DtypeComplexConditional)

    def __hash__(self):
        return hash(type(self).__name__)


class DtypeReal(DtypeExtendedReal, DtypeComplex):
    
    is_real = True
    is_finite = True
    
    @property
    def universalSet(self):
        from sympy.sets.fancysets import Reals
        return Reals
    
    def as_Set(self):
        from sympy.sets.fancysets import Reals
        return Reals

    def __str__(self):
        return 'real'
    
    @property
    def dict(self):
        return {'real': True}

    def __eq__(self, other):
        return isinstance(other, DtypeReal)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeRealConditional(**kwargs)

    def extended_type(self):
        return self.extended_real


class DtypeRealConditional(DtypeReal):

    def as_Set(self):
        if self.assumptions.get('positive') is True:
            ...
        from sympy import Interval
        return Interval(-S.Infinity, S.Infinity)

    def __init__(self, **assumptions):
        self.assumptions = assumptions
    
    def __str__(self):
        return Dtype.__str__(self, 'real')
    
    @property
    def dict(self):
        assumptions = {**self.assumptions}
        assumptions['real'] = True
        return assumptions

    def __eq__(self, other):
        return isinstance(other, DtypeRealConditional)

    def __hash__(self):
        return hash(type(self).__name__)

    def __contains__(self, x):
        if isinstance(x, DtypeReal):
            assumptions = x.dict
            if 'nonnegative' in self.assumptions:
                if 'positive' in assumptions:
                    return True
                elif 'nonnegative' in assumptions:
                    return True
            elif 'nonpositive' in self.assumptions:
                if 'negative' in assumptions:
                    return True
                elif 'nonpositive' in assumptions:
                    return True
            elif 'negative' in self.assumptions:
                if 'negative' in assumptions:
                    return True
            elif 'positive' in self.assumptions:
                if 'nonpositive' in assumptions:
                    return True
            
        return False


class DtypeRational(DtypeExtendedRational, DtypeReal):

    is_rational = True
    is_finite = True
    
    @property
    def universalSet(self):
        from sympy import Interval
        return Interval(S.NegativeInfinity, S.Infinity, rational=True)

    def as_Set(self):
        return S.Rationals

    def __str__(self):
        return 'rational'
    
    @property
    def dict(self):
        return {'rational': True}

    def __eq__(self, other):
        return isinstance(other, DtypeRational)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeRationalConditional(**kwargs)
    
    def extended_type(self):
        return self.extended_rational


class DtypeRationalConditional(DtypeRational):

    def as_Set(self):
        if self.assumptions.get('positive') is True:
            ...
        return S.Rationals

    def __init__(self, **assumptions):
        self.assumptions = assumptions
    
    def __str__(self):
        return Dtype.__str__(self, 'rational')
    
    @property
    def dict(self):
        assumptions = {**self.assumptions}
        assumptions['rational'] = True
        return assumptions

    def __eq__(self, other):
        return isinstance(other, DtypeRationalConditional)

    def __hash__(self):
        return hash(type(self).__name__)


class DtypeInteger(DtypeExtendedInteger, DtypeRational):
    
    is_DtypeInteger = True
    is_integer = True
    is_finite = True
    
    @property
    def universalSet(self):
        from sympy import Range
        return Range(S.NegativeInfinity, S.Infinity)
    
    def as_Set(self):
        from sympy.sets import Integers
        return Integers

    def __str__(self):
        return 'integer'
    
    @property
    def dict(self):
        return {'integer': True}

    def __eq__(self, other):
        return isinstance(other, DtypeInteger)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeIntegerConditional(**kwargs)

    def extended_type(self):
        return self.extended_integer


class DtypeIntegerConditional(DtypeInteger):

    def as_Set(self):
        positive = self.assumptions.get('positive')
        if positive:
            from sympy.sets import PositiveIntegers
            return PositiveIntegers
        nonnegative = self.assumptions.get('nonnegative')
        if nonnegative:
            from sympy.sets import NonnegativeIntegers
            return NonnegativeIntegers
        
        from sympy import Range
        negative = self.assumptions.get('negative')
        if negative:
            return Range(S.NegativeInfinity, 0)
        nonpositive = self.assumptions.get('nonpositive')
        if nonpositive:
            return Range(S.NegativeInfinity, 1)

        even = self.assumptions.get('even')
        odd = self.assumptions.get('odd')
        
        if even:
            return Range(S.PositiveInfinity, step=2, integer=True) | Range(S.NegativeInfinity, 0, step=2, integer=True)
        if odd:
            return Range(1, S.PositiveInfinity, step=2, integer=True) | Range(S.NegativeInfinity, -1, step=2, integer=True)
        return S.Integers

    def __init__(self, **assumptions):
        self.assumptions = assumptions
    
    def __str__(self):
        return Dtype.__str__(self, 'integer')
    
    @property
    def dict(self):
        assumptions = {**self.assumptions}
        assumptions['integer'] = True
        return assumptions

    def __eq__(self, other):
        return isinstance(other, DtypeIntegerConditional)

    def __hash__(self):
        return hash(type(self).__name__)

    def __add__(self, start):
        from sympy import Range, oo
        if 'nonnegative' in self.assumptions:
            if start != 0:
                return self.integer(domain=Range(start, oo)) 
            return self
        return self.integer


class DtypeSet(Dtype):
    is_set = True
    
    def __init__(self, etype):
        self.etype = etype

    def __str__(self):
        return '%s.set' % self.etype
    
    @property
    def is_finite(self):
        return self.etype.is_finite
    
    @property
    def dict(self):
        return {'etype': self.etype}

    def __eq__(self, other):
        return isinstance(other, DtypeSet) and self.etype == other.etype

    def __hash__(self):
        return hash((type(self).__name__, self.etype))
    
    def _has(self, pattern):
        return self.etype._has(pattern)
    
    def _subs(self, old, new, **hints):
        etype = self.etype._subs(old, new)
        if etype is not self.etype:
            return type(self)(etype)
        return self

    @property
    def is_integer(self):
        return self.etype.is_integer
    
    @property
    def is_extended_integer(self):
        return self.etype.is_extended_integer
    
    @property
    def is_super_integer(self):
        return self.etype.is_super_integer
    
    @property
    def is_rational(self):
        return self.etype.is_rational
    
    @property
    def is_extended_rational(self):
        return self.etype.is_extended_rational
    
    @property
    def is_hyper_rational(self):
        return self.etype.is_hyper_rational
    
    @property
    def is_super_rational(self):
        return self.etype.is_super_rational
    
    @property
    def is_real(self):
        return self.etype.is_real

    @property
    def is_extended_real(self):
        return self.etype.is_extended_real
    
    @property
    def is_hyper_real(self):
        return self.etype.is_hyper_real
    
    @property
    def is_super_real(self):
        return self.etype.is_super_real
    
    @property
    def is_extended_positive(self):
        return self.etype.is_extended_positive

    @property
    def is_extended_negative(self):
        return self.etype.is_extended_negative
    
    @property
    def is_complex(self):
        return self.etype.is_complex

    @property
    def is_extended_complex(self):
        return self.etype.is_extended_complex

    @property
    def is_hyper_complex(self):
        return self.etype.is_hyper_complex
    
    
class DtypeMatrix(Dtype):
    
    @property
    def is_finite(self):
        return self.dtype.is_finite
    
    @property
    def is_integer(self):
        return self.dtype.is_integer

    @property
    def is_rational(self):
        return self.dtype.is_rational

    @property
    def is_real(self):
        return self.dtype.is_real

    @property
    def is_complex(self):
        return self.dtype.is_complex

    @property
    def universalSet(self):
        from sympy import CartesianSpace
        return CartesianSpace(self.dtype.universalSet, *self.shape)

    def as_Set(self):
        from sympy.sets.sets import CartesianSpace
        return CartesianSpace(self.dtype.as_Set(), *self.lengths)

    def __init__(self, dtype, shape, **kwargs):
        self.dtype = dtype
        self.lengths = tuple(shape)
        self.assumptions = kwargs

    @property
    def shape(self):
        return self.lengths

    def __str__(self):
        if self.assumptions:
            return '%s[%s]%s' % (self.dtype, ', '.join(str(s) for s in self.shape), str(self.assumptions))
        return '%s[%s]' % (self.dtype, ', '.join(str(length) for length in self.shape))
    
    def slice(self, indices):
        if isinstance(indices, (tuple, Tuple, list)):
            diff = len(self.shape) - len(indices)
        elif isinstance(indices, slice):
            start, stop = indices.start, indices.stop
            shape = (stop - start,) + self.shape[1:]
            return Basic.__new__(DtypeMatrix, self.dtype, shape)
        else:
            diff = len(self.shape) - 1
            
        if diff == 1:
            return DtypeMatrix(self.dtype, (self.shape[-1],))
        if diff == 0:
            return self.dtype
        return DtypeMatrix(self.dtype, self.shape[-diff:])

    def __getitem__(self, length):
        if isinstance(length, (tuple, Tuple, list)):
            length = tuple(length)
            return DtypeMatrix(self.dtype, self.shape + length)
        return DtypeMatrix(self.dtype, self.shape + (length,))

    @property
    def dict(self):
        dic = self.dtype.dict
        dic['shape'] = self.shape
        dic.update(self.assumptions)
        return dic

    def __eq__(self, other):
        return isinstance(other, DtypeMatrix) and self.shape == other.shape and self.dtype == other.dtype

    def __hash__(self):
        return hash((type(self).__name__, self.dtype, self.shape))
    
    def transpose(self, *args): 
        if not args:
            args = (-2, -1)
        i, j = args
        [*lengths] = self.lengths
        lengths[i], lengths[j] = lengths[j], lengths[i]
        return DtypeMatrix(self.dtype, lengths)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeMatrix(self.dtype, self.lengths, **kwargs)

    def _has(self, pattern):
        return any(l._has(pattern) for l in self.lengths)

    def _subs(self, old, new, **hints):
        hit = False
        dtype = self.dtype._subs(old, new)
        if dtype is not self.dtype:
            hit = True
            
        lengths = []
        for l in self.lengths:
            _l = l._subs(old, new)
            if _l != l:
                hit = True
            lengths.append(_l)
            
        if hit:
            return type(self)(dtype, tuple(lengths))
        
        return self

    def __contains__(self, other):
        if isinstance(other, DtypeMatrix):
            if other.shape == self.shape:
                return other.dtype in self.dtype

    def python_definition(self, free_symbols, random_symbols):
        definition = []
        for s in self.shape:
            if isinstance(s, Basic):
                Symbol.definition_append(definition, s.python_definition(free_symbols, random_symbols))
        return definition


class DtypeBoolean(Dtype):
    is_bool = True
    
    def __str__(self):
        return 'bool'
    
    @property
    def dict(self):
        return {'bool': True}

    def __eq__(self, other):
        return isinstance(other, DtypeBoolean)

    def __hash__(self):
        return hash(type(self).__name__)


class DtypeDistribution(Dtype):

    is_distribution = True
    
    def __str__(self):
        return 'distribution'
    
    @property
    def dict(self):
        return {'random': True}

    def __eq__(self, other):
        return isinstance(other, DtypeDistribution)

    def __hash__(self):
        return hash(type(self).__name__)


class DtypeTuple(Dtype):

    is_tuple = True
    
    def __init__(self, *dtype):
        self.dtype = dtype

    def __str__(self):
        return 'tuple'
    
    @property
    def dict(self):
        return {'dtype': self.dtype}

    def __eq__(self, other):
        return isinstance(other, DtypeTuple)

    def __hash__(self):
        return hash(type(self).__name__)


class DtypeType(Dtype):

    is_type = True
    
    def __init__(self, type):
        self.type = type

    def __str__(self):
        return self.type.__name__ + '.etype'
    
    @property
    def dict(self):
        return {'domain': self.type}

    def __eq__(self, other):
        return isinstance(other, DtypeType) and self.type == other.type

    def __hash__(self):
        return hash((self.__class__, self.type))


dtype = Dtype()
