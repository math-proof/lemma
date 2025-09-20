from sympy.core.cache import cacheit
r"""Module that defines indexed objects

The classes ``IndexedBase``, ``Indexed``, and ``Idx`` represent a
matrix element ``M[i, j]`` as in the following diagram::

       1) The Indexed class represents the entire indexed object.
                  |
               ___|___
              '       '
               M[i, j]
              /   \__\______
              |             |
              |             |
              |     2) The Idx class represents indices; each Idx can
              |        optionally contain information about its range.
              |
        3) IndexedBase represents the 'stem' of an indexed object, here `M`.
           The stem used by itself is usually taken to represent the entire
           array.

There can be any number of indices on an Indexed object.  No
transformation properties are implemented in these Base objects, but
implicit contraction of repeated indices is supported.

Note that the support for complicated (i.e. non-atomic) integer
expressions as indices is limited.  (This should be improved in
future releases.)

Examples
========

To express the above matrix element example you would write:

>>> from sympy import symbols, IndexedBase, Idx
>>> M = IndexedBase('M')
>>> i, j = symbols('i j', cls=Idx)
>>> M[i, j]
M[i, j]

Repeated indices in a product implies a summation, so to express a
matrix-vector product in terms of Indexed objects:

>>> x = IndexedBase('x')
>>> M[i, j]*x[j]
M[i, j]*x[j]

If the indexed objects will be converted to component based arrays, e.g.
with the code printers or the autowrap framework, you also need to provide
(symbolic or numerical) dimensions.  This can be done by passing an
optional shape parameter to IndexedBase upon construction:

>>> dim1, dim2 = symbols('dim1 dim2', integer=True)
>>> A = IndexedBase('A', shape=(dim1, 2*dim1, dim2))
>>> A.shape
(dim1, 2*dim1, dim2)
>>> A[i, j, 3].shape
(dim1, 2*dim1, dim2)

If an IndexedBase object has no shape information, it is assumed that the
array is as large as the ranges of its indices:

>>> n, m = symbols('n m', integer=True)
>>> i = Idx('i', m)
>>> j = Idx('j', n)
>>> M[i, j].shape
(m, n)
>>> M[i, j].ranges
[(0, m - 1), (0, n - 1)]

The above can be compared with the following:

>>> A[i, 2, j].shape
(dim1, 2*dim1, dim2)
>>> A[i, 2, j].ranges
[(0, m - 1), None, (0, n - 1)]

To analyze the structure of indexed expressions, you can use the methods
get_indices() and get_contraction_structure():

>>> from sympy.tensor import get_indices, get_contraction_structure
>>> get_indices(A[i, j, j])
({i}, {})
>>> get_contraction_structure(A[i, j, j])
{(j,): {A[i, j, j]}}

See the appropriate docstrings for a detailed explanation of the output.
"""

#   TODO:  (some ideas for improvement)
#
#   o test and guarantee numpy compatibility
#      - implement full support for broadcasting
#      - strided arrays
#
#   o more functions to analyze indexed expressions
#      - identify standard constructs, e.g matrix-vector product in a subexpression
#
#   o functions to generate component based arrays (numpy and sympy.Matrix)
#      - generate a single array directly from Indexed
#      - convert simple sub-expressions
#
#   o sophisticated indexing (possibly in subclasses to preserve simplicity)
#      - Idx with range smaller than dimension of Indexed
#      - Idx with stepsize != 1
#      - Idx with step determined by function call

from sympy.core import Expr, Tuple, Symbol, sympify, S
from sympy.core.compatibility import (is_sequence, NotIterable,
                                      Iterable)
from sympy.core.sympify import _sympify


class IndexException(Exception):
    pass


class Indexed(Expr):
    """Represents a mathematical object with indices.

    >>> from sympy import Indexed, IndexedBase, Idx, symbols
    >>> i, j = symbols('i j', cls=Idx)
    >>> Indexed('A', i, j)
    A[i, j]

    It is recommended that ``Indexed`` objects be created via ``IndexedBase``:

    >>> A = IndexedBase('A')
    >>> Indexed('A', i, j) == A[i, j]
    True

    """
    is_commutative = True
    is_Atom = True

    @property
    def is_symbol(self):
        return self.base.is_symbol
    
    @classmethod
    def class_key(cls):
        return 3, 0, cls.__name__

    def __iter__(self):
        raise TypeError

    def __setitem__(self, indices, value):
        if isinstance(indices, tuple):
            if isinstance(indices[-1], slice):
                value, *slices = value.of(Sliced)
                
                size = len(slices)
                for i in range(size):
                    start, stop = slices[i].of(Tuple)
                    index = indices[i - size]
                    assert index.start == start
                    assert index.stop == stop
                    
                indices = indices[:-size]
                self[indices] = value
            else:
                args = value.of(Indexed)
                assert self == args[0]
                assert args[1:] == indices
        else:
            if isinstance(indices, slice):
                base, sliced = value.of(Sliced)
                start, stop = sliced.of(Tuple)
                assert indices.start == start
                assert indices.stop == stop
                
                assert self == base

            else:
                base, index = value.of(Indexed)
                assert self == base
                assert index == indices

    def __getitem__(self, indices, **kw_args):
        if (indices := self.simplify_indices(indices)) is None:
            return self
        
        if isinstance(indices, tuple):
            for pivot, index in enumerate(indices):
                if isinstance(index, Tuple):
                    break
            else:
                pivot += 1
                
            indices, slices = indices[:pivot], indices[pivot:]
            if slices:
                if indices:
                    return self[indices][slices]
                
                for pivot, index in enumerate(slices):
                    if not isinstance(index, Tuple):
                        break
                else:
                    pivot += 1
                    
                slices, indices = slices[:pivot], slices[pivot:]
                if indices:
                    index, *indices = indices
                    self = SlicedIndexed(self, *slices, index)
                    if indices:
                        self = self[indices]
                    return self
                
                return Sliced(self, *slices)
            
            indices = self.indices + indices
            
        elif isinstance(indices, Tuple):
            start, stop, step = indices.slice_args
            if start is None:
                start = 0
                
            if stop is None:
                stop = self.shape[0]
                
            if step is None:
                step = S.One
                
            if start == stop - 1:
                return Indexed(self, start, **kw_args)
            
            if start == 0 and stop == self.shape[0] and step == 1:
                return self
            
            return Sliced(self, indices, **kw_args)
        else:
            indices = self.indices + (indices,)
            
        assert len(indices) <= len(self.base.shape)
        return Indexed(self.base, *indices, **kw_args)

    def image_set(self):
        definition = self.base.definition
        if definition is None:
            return
        return definition[self.indices].image_set()

    def element_symbol(self, excludes=set()):
        etype = self.etype
        if etype is None:
            return

        return self.generate_var(excludes=excludes, **etype.dict)

# performing other in self
    def __contains__(self, other):
        if other.is_Intersection:
            if self in other._argset:
                return True
        definition = self.base.defun()
        if definition  is not None:
            try: 
                return other in definition [self.indices]
            except TypeError:
                ...
        
    def _dummy_eq(self, other):
        return self == other

    def structurally_equal(self, other):
        if isinstance(other, (Symbol, Indexed, Sliced)):
            return self.shape == other.shape
        return False

    @cacheit
    def __new__(cls, base, *args, **kw_args):
        from sympy.tensor.array.ndim_array import NDimArray
        from sympy.matrices.matrices import MatrixBase

        if not args:
            return base
#             raise IndexException("Indexed needs at least one index.")
        if isinstance(base, str):
            base = Symbol(base, shape=(S.Infinity,))
        elif isinstance(base, Symbol):
            assert base.shape
        elif not hasattr(base, '__getitem__') and not base.is_Symbol:
            assert len(base.shape) >= len(args)
        args = list(map(sympify, args))
        
        if isinstance(base, (NDimArray, Tuple, MatrixBase)) and all([i.is_number for i in args]):
            if len(args) == 1:
                return base[args[0]]
            else:
                return base[args]
        if base.is_Stack:
            return base[args]
            
        if len(args) == 1 and args[0].is_Piecewise:
            piecewise = args[0]
            return piecewise.func(*((cls(base, e), c) for e, c in piecewise.args))
            
        return Expr.__new__(cls, base, *args, **kw_args)

    @property
    def name(self):
        return str(self)

    @property
    def _diff_wrt(self):
        """Allow derivatives with respect to an ``Indexed`` object."""
        return True

    @property
    def is_set(self):
        return self.base.type.slice(self.indices).is_set

    def _eval_derivative(self, wrt):
        from sympy.tensor.array.ndim_array import NDimArray
        from sympy.functions.special.tensor_functions import KroneckerDelta
        
        if isinstance(wrt, Indexed) and wrt.base == self.base:
            if len(self.indices) != len(wrt.indices):
                msg = "Different # of indices: d({!s})/d({!s})".format(self,
                                                                       wrt)
                raise IndexException(msg)
            result = S.One
            for index1, index2 in zip(self.indices, wrt.indices):
                result *= KroneckerDelta(index1, index2)
            return result
        elif isinstance(self.base, NDimArray):
            from sympy.tensor.array import derive_by_array
            return Indexed(derive_by_array(self.base, wrt), *self.args[1:])
        else:
            if Tuple(self.indices).has(wrt):
                return S.NaN
            return S.Zero

    base = property(lambda self: self.args[0])
    indices = property(lambda self: self.args[1:])
    index = property(lambda self: self.args[1])
    shape = property(lambda self: self.base.shape[len(self.indices):])
    
    @property
    def rank(self):
        """
        Returns the rank of the ``Indexed`` object.

        Examples
        ========

        >>> from sympy import Indexed, Idx, symbols
        >>> i, j, k, l, m = symbols('i:m', cls=Idx)
        >>> Indexed('A', i, j).rank
        2
        >>> q = Indexed('A', i, j, k, l, m)
        >>> q.rank
        5
        >>> q.rank == len(q.indices)
        True

        """
        return len(self.args) - 1

    @property
    def ranges(self):
        """Returns a list of tuples with lower and upper range of each index.

        If an index does not define the data members upper and lower, the
        corresponding slot in the list contains ``None`` instead of a tuple.

        Examples
        ========

        >>> from sympy import Indexed,Idx, symbols
        >>> Indexed('A', Idx('i', 2), Idx('j', 4), Idx('k', 8)).ranges
        [(0, 1), (0, 3), (0, 7)]
        >>> Indexed('A', Idx('i', 3), Idx('j', 3), Idx('k', 3)).ranges
        [(0, 2), (0, 2), (0, 2)]
        >>> x, y, z = symbols('x y z', integer=True)
        >>> Indexed('A', x, y, z).ranges
        [None, None, None]

        """
        ranges = []
        for i in self.indices:
            sentinel = object()
            upper = getattr(i, 'upper', sentinel)
            lower = getattr(i, 'lower', sentinel)
            if sentinel not in (upper, lower):
                ranges.append(Tuple(lower, upper))
            else:
                ranges.append(None)
        return ranges

    def _sympystr(self, p):
        indices = list(map(p._print, self.indices))
        return "%s[%s]" % (p._print(self.base), ", ".join(indices))

    def _lean(self, p):
        indices = list(map(p._print, self.indices))
        return "%s[%s]" % (p._print(self.base), ", ".join(indices))

    def _latex(self, p, **kwargs):
        base = self.base
        shape = base.shape
        exp = None
        if base.is_Symbol:
            import re
            if m := re.match(r"(\w+)\^([\w-]+)", base.name):
                tex_base, exp = m.groups()

        if exp is None:
            tex_base = base._latex(p, **kwargs)

        indices = [*self.indices]
        
        for i, index in enumerate(indices):
            length = shape[i]
            if index.is_Add:
                if length in index.args:
                    negative_index = index - length
                    if negative_index.is_extended_negative:
                        indices[i] = negative_index
                
        if base.is_Mul or base.is_Add or base.is_MatMul:
            tex_base = r"\left(%s\right)" % tex_base

        if exp is None:
            return '{%s}_{%s}' % (tex_base, ','.join(map(p._print, indices)))
        
        return '{%s}_{%s}^{%s}' % (tex_base, ','.join(map(p._print, indices)), exp)

    @cacheit
    def _eval_free_symbols(self):
        base = self.base
        indices_free_symbols = {fs for i in self.indices for fs in i.free_symbols}
        base_free_symbols = indices_free_symbols | base.free_symbols
        if 'definition' in base._assumptions or base.is_AppliedUndef:
            ...
        else: 
            base_free_symbols.add(self)
        return base_free_symbols

    @property
    def expr_free_symbols(self):
        return {self}
    
    # return expr._has(self)
    def has_match(self, expr):
        from sympy.core.symbol import Wild
        if expr.is_Indexed and expr.base == self.base:
            from sympy import Unequal
            for _index, index in zip(expr.indices, self.indices):
                if isinstance(index, Wild):
                    return False

                if Unequal(_index, index):
                    return False
# it is still possible for them to be equal!
            return True

        if expr.is_Sliced:
            if expr.base == self.base:
                if len(self.indices) == 1:
                    start, stop = expr.index
                    index_fixed, *_ = self.indices
    
                    if isinstance(index_fixed, Wild):
                        return False
    
                    if stop <= index_fixed or start > index_fixed:
                        return False
                    # it is possible for them to be equal!
                    return True
            elif expr.base.is_Indexed and expr.base.base == self.base:
                from sympy import Unequal
                _indices = expr.base.indices
                indices = self.indices
                for _index, index in zip(_indices, indices):
                    if Unequal(_index, index):
                        return False
                
                for _index, index in zip(expr.indices, indices[len(_indices):]):
                    start, stop, step = _index.slice_args
                    if index < start or index >= stop:
                        return False
    # it is still possible for them to be equal!
                return True
            else:
                base = expr.base.definition
                if base is not None and base._has(self):
                    return True
            
        if isinstance(expr, Symbol) and expr == self.base:
            if len(self.indices) == 1:
                start, stop = 0, expr.shape[-1]
                index_fixed, *_ = self.indices

                if isinstance(index_fixed, Wild):
                    return False

                if stop <= index_fixed or start > index_fixed:
                    return False
                # it is possible for them to be equal!
                return True
            
        return False

    @cacheit
    def _has(self, pattern):
        if pattern.is_Tuple:
            return any(self._has(pattern) for pattern in pattern)
        """Helper for .has()"""
        if pattern.is_Indexed or pattern.is_Sliced:
            if pattern.has_match(self):
                return True
                
        if any(arg._has(pattern) for arg in self.indices):
            return True
        from sympy.core.assumptions import ManagedProperties
        
        if not isinstance(pattern, ManagedProperties) and hasattr(pattern, 'has_match') and pattern.has_match(self):
            return True
            
        if isinstance(pattern, ManagedProperties) or pattern.is_FunctionClass:
            return self.base._has(pattern)
        else: 
            if self.base.is_AppliedUndef:
                return self.base._has(pattern)
                                
            definition = self.definition
            if definition is not None:
                return definition._has(pattern)
            if self.base.is_Transpose:
                if self.base.arg == pattern:
                    return True
        
        return False

    def _subs(self, old, new, **hints):
        if self.base == old:
            indices = tuple(index._subs(old, new) for index in self.indices)
            return new[indices]

        this = Expr._subs(self, old, new, **hints)
        if this != self:
            return this
        if hints.get('symbol') is not False:
            if self.base.is_AppliedUndef:
                ...
            else:
                definition = self.definition
                if definition is not None:
                    this = definition._subs(old, new, **hints)
                    if this != definition:
                        return this
        if old.is_Indexed and old.base == self.base:
            indices = old.indices
            self_indices = self.indices
            if self_indices[:len(indices)] == indices:
                return new[self_indices[len(indices):]]
            
        return self

    def _subs_sliced(self, old, new, **hints): 
        if self.base == old.base and len(self.indices) >= len(old.indices):
            self_indices = self.indices
            old_indices = old.indices
            
            if len(self_indices) > len(old_indices):
                old_indices = [*old_indices]  # make a copy first
                shape = self.base.shape
                while len(self_indices) > len(old_indices): 
                    old_indices.append((0, shape[len(old_indices)]))
#             elif len(self_indices) < len(old_indices):
                # could not substitute for an index with fewer args than that of a slice
                    
            indices = []
            
            from sympy import Range
            for k, (start, stop) in zip(self_indices, old_indices):
                if Range(start, stop).conditionally_contains(k):
                    indices.append(k - start)
                else: 
                    break
            else: 
                return new[tuple(indices)]

        return Expr._subs_sliced(self, old, new, **hints)

    def _eval_is_random(self):
        return any(arg.is_random for arg in self.args)

    @property
    def distribution(self):
        distribution = self.base.distribution
        if distribution is not None:
            return distribution
                         
        definition = self.definition
        if definition is not None: 
            if self.is_integer:
                from sympy.stats.drv_types import AbstractDiscreteDistribution
                return AbstractDiscreteDistribution(definition.function)
            else: 
                from sympy.stats.crv_types import AbstractContinuousDistribution
                return AbstractContinuousDistribution(definition) 

    @property
    def dtype(self):
        return self.base.dtype

    @cacheit
    def _eval_domain_defined(self, x, **_):
        if x.dtype.is_set:
            return x.universalSet
                
        if not x.shape:
            for i, index in enumerate(self.indices):
                if index._has(x):
                    diff = x - index
                    if diff._has(x):
                        continue
                    from sympy.sets.fancysets import Range
                    domain = Range(diff, self.base.shape[i] + diff)
                    return x.domain & domain
                
        if not self.base.is_AppliedUndef:
            definition = self.definition
            if definition is not None:
                return definition.domain_defined(x)
            
        domain = x.domain
         
        for index in self.indices:
            domain &= index.domain_defined(x)
        return domain

    @property
    def definition(self):
        return self.defun()
    
    @cacheit
    def defun(self):
        try:
            definition = self.base.defun()
            return definition[self.indices]
        except:
            ...
       
    def _eval_is_extended_integer(self):
        if not hasattr(self.base, 'is_extended_integer') and self.base.definition is not None:
            return self.base.definition.is_extended_integer
        return self.base.is_extended_integer
    
    def _eval_is_extended_real(self):
        return self.base.is_extended_real

    def _eval_is_hyper_real(self):
        return self.base.is_hyper_real
    
    def _eval_is_super_real(self):
        return self.base.is_super_real

    def _eval_is_extended_complex(self):
        return self.base.is_extended_complex

    def _eval_is_extended_negative(self):
        return self.base.is_extended_negative

    def _eval_is_extended_positive(self):
        return self.base.is_extended_positive

    def _eval_is_finite(self):
        return self.base.is_finite

    def _eval_is_zero(self):
        return self.base.is_zero

    def copy(self, **kwargs):
        return self.base.copy(**kwargs)[self.indices]

    def equality_defined(self):
        from sympy import Equal
        return Equal(self, self.definition, evaluate=False)

    def _eval_determinant(self, **kwargs):
        definition = self.definition
        if definition is not None:
            return definition._eval_determinant(**kwargs)

    def generate_int_limit(self, *args, **kwargs):
        definition = self.definition
        if definition is not None:
            return definition.generate_int_limit(*args, **kwargs) 
        return Expr.generate_int_limit(self, *args, **kwargs)
      
    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            if len(self.shape) < 2:
                return self
            
            definition = self.definition
            if definition is not None:
                if definition.T == definition:
                    return self

    @property
    def domain(self): 
        if self.is_set:
            return self.universalSet
        definition = self.defun()
        if definition is not None:
            if self is not definition:
                return definition.domain
        
        from sympy import Interval, Range
        domain = self.base.domain_assumed
        if domain is None:
            
            assumptions = self.base.assumptions0
            integer = assumptions.pop('integer', None)
            if integer:
                domain = Range(**assumptions)
            elif self.is_real:
                domain = Interval(**assumptions)
            elif self.is_extended_real:
                from sympy import ExtendedReals
                domain = ExtendedReals
            elif self.is_complex:
                domain = S.Complexes
            elif self.is_extended_complex:
                domain = S.ExtendedComplexes
            else:
                from sympy import SuperComplexes
                domain = SuperComplexes
            
        shape = self.shape
        if not shape:
            return domain
        from sympy.sets.sets import CartesianSpace
        return CartesianSpace(domain, *shape)

    @property
    def domain_assumed(self):
        return self.base.domain_assumed

    @property
    def is_given(self): 
        return self.base.is_given
#         if self.base.is_given:
#             return True
#         return all(index.is_given for index in self.indices)

    as_boolean = Symbol.as_boolean

    def condition_set(self):
        definition = self.definition
        if definition is None:
            return
        return definition.condition_set()

    def doit(self, **hints):
        indices = tuple(index.doit(**hints) for index in self.indices)
        if indices == self.indices:
            return self
        return self.base[indices] 

    def is_continuous_at(self, *args):
        definition = self.definition
        if definition is None:
            return True
        return definition.is_continuous_at(*args)
    
    def invert(self):
        from sympy.logic.boolalg import Not
        return Not(self)
    
    def of(self, cls):
        if cls.is_IndexedOperator and cls.func.is_Symbol:
            return self.of(Indexed[(Symbol,) + cls.args])
        return Expr.of(self, cls)
 
    of_simple_poly = Symbol.of_simple_poly
    
    monotonicity = Symbol.monotonicity
    
    def expand_indices(self, limits, expr=None):
        base, *indices = self.args
        
        indices_transformed = [*indices]
        hit = False
        for limit in limits:
            i, *ab = limit
            if i == self:
                return self

            if not i.is_integer:
                continue

            if len(ab) == 2 and not ab[1].is_set:
                if args := expand_indices(limit, indices_transformed):
                    t, args = args
                    indices_transformed[t] = args
                    hit = True

            elif not ab and expr is not None:
                domain = expr.domain_defined(i)
                if domain.is_Range:
                    if args := expand_indices((i, *domain.args), indices_transformed):
                        t, args = args
                        indices_transformed[t] = args
                        hit = True
                
        if hit:
            return base[tuple(indices_transformed)]
        
        return self
                                
    @staticmethod
    def simplify_Lamda(self, squeeze=False):
        variables = tuple(x for x, *_ in self.limits[::-1])
        expr = self.expr
        if expr.is_set:
            if expr.args[-len(variables):] == variables:
                base = expr.base[expr.indices[:-len(variables)]]
                for x, *ab in reversed(self.limits):
                    if len(ab) == 1:
                        return self
                    
                    if len(ab) == 2:
                        a, b = ab
                        base = base[a:b]
                        
                    else:
                        domain = x.domain
                        if domain.is_Range and domain.start == 0 and domain.stop == base.shape[0]:
                            continue
                        
                        return self
                        
                return base
        else:
            indices = expr.indices
            if len(variables) == 1:
                var, = variables
                try:
                    i = indices.index(var)
                    _, *ab = self.limits[0]
                    if ab :
                        if len(ab) == 2:
                            if i == len(indices) - 1:
                                indexed = expr.base[indices[:-1]]
                                zero, b = ab
                                assert zero.is_zero
                                shape = b
                                if expr.base.shape[0] != shape:
                                    return indexed[:shape]
                                return indexed
                            else:
                                indexed = expr.base[indices[:i]]
                                zero, b = ab
                                assert zero.is_zero
                                shape = b
                                
                                rest_indices = indices[i + 1:]
                                return indexed[(slice(0, shape),) + rest_indices]
                                                            
                        else:
                            [domain] = ab
                            if i == len(indices) - 1:
                                indexed = expr.base[indices[:-1]]
                                start, stop, step = domain.args
                                if start.is_zero:
                                    if step.is_One:
                                        if expr.base.shape[0] != stop:
                                            return indexed[:stop]
                                        return indexed
                                    else:
                                        return indexed[:stop:step]
                                else:
                                    if step.is_One:
                                        return indexed[start:stop]
                                    else:
                                        return indexed[start:stop:step]
                            else:
                                indexed = expr.base[indices[:i]]
                                rest_indices = indices[i + 1:]
                                start, stop, step = domain.args
                                if start.is_zero:
                                    if step.is_One:
                                        return indexed[(slice(0, stop),) + rest_indices]
                                    else:
                                        return indexed[(slice(0, stop, step),) + rest_indices]
                                else:
                                    if step.is_One:
                                        return indexed[(slice(start, stop),) + rest_indices]
                                    else:
                                        return indexed[(slice(start, stop, step),) + rest_indices]
                                
                    
                except ValueError:
                    validIndices = [(i, index) for i, index in enumerate(expr.indices) if index._has(var)]
                    if len(validIndices) == 1:
                        [[i, index]] = validIndices
                        # index = step * var + start
                        start, step = index.of_simple_poly(var)
                        if step == 1:
                            _, *ab = self.limits[0]
                            if ab:
                                if len(ab) == 2:
                                    zero, shape = ab
                                    assert zero.is_zero
                                    step = 1
                                else:
                                    [domain] = ab
                                    zero, shape, step = domain.args
                            else:
                                shape = self.shape[0]

                            return expr.base[indices[:i] + (slice(start, shape + start, step),) + indices[i + 1:]]
                            
                        elif step:
                            _, *ab = self.limits[0]
                            if ab:
                                if len(ab) == 2:
                                    zero, shape = ab
                                    assert zero.is_zero
                                    if shape.is_Ceil:
                                        stop = shape.arg * step + start
                                        if not stop._has(var):
                                            return expr.base[indices[:i] + (slice(start, stop, step),) + indices[i + 1:]]
                
            if expr.args[-len(variables):] == variables:
                return expr.base[indices[:-len(variables)]]
    
            [*indices] = indices
            j = len(indices)
            
            hit = False
            for i, var in enumerate(self.variables):
                for j in range(j - 1, -1, -1):
                    if indices[j] == var:
                        break
                else:
                    break
                
                hit = True
                ab = self.limits[i][1:]
                if len(ab) == 2:
                    a, b = ab
                    if a == 0:
                        indices[j] = slice(b)
                    else:
                        indices[j] = slice(*ab)
                elif not ab:
                    indices[j] = slice(self.shape[-i - 1])
                else:
                    [domain] = ab
                    indices[j] = slice(*domain.args)
            else:
                i += 1
                
            if hit:
                return expr.base[indices]
                
        return self
        
    @property
    def var(self):
        assert self.base.is_random
        assert not any(index.is_random for index in self.indices)
        return self.base.var[self.indices]

    @property
    def surrogate(self):
        assert self.base.is_random
        assert not any(index.is_random for index in self.indices)
        return self.base.surrogate[self.indices]

    def __and__(self, other):
        """Overloading for & operator"""
        if self.is_random and other.is_random:
            if not other.is_bool:
                other = other.as_boolean()
            return self.as_boolean() & other
        
        return super(Indexed, self).__and__(other)

# performing other.indices in self.indices
    def index_contains(self, other):
        if other.is_Sliced or other.is_SlicedIndexed:
            return self.index_contains(other.base)

        if other.is_Indexed:
            if self.base != other.base:
                return
            return indices_contains_indices(self.indices, other.indices)

# performing indices intersection
    def index_intersect(self, other):
        if other.is_Sliced or other.is_SlicedIndexed:
            if self.index_contains(other.base):
                return other
            return

        if other.is_Indexed:
            if self.base != other.base:
                return
            
            if indices_contains_indices(self.indices, other.indices):
                return other

            if indices_contains_indices(other.indices, self.indices):
                return self

# performing indices complement
    def index_complement(self, other):
        if other.is_Sliced or other.is_SlicedIndexed:
            if other.index_contains(self):
                return
            else:
                return self

        if other.is_Indexed:
            if self.base == other.base:
                if indices_contains_indices(self.indices, other.indices):
                    return

        return self

    @property
    def is_bounded(self):
        self = self.base
        if self.is_Symbol:
            return self._eval_is_bounded()

    @property
    def domain_bounded(self):
        base = self.base
        if base.is_Symbol: 
            from sympy import CartesianSpace
            from sympy import Interval, oo, Range
            if 'domain' in base._assumptions:
                domain = base._assumptions['domain']
            elif base.is_positive:
                if base.is_integer:
                    domain = Range(1, oo)
                else:
                    domain = Interval(0, oo, left_open=True)
            elif base.is_negative:
                if base.is_integer:
                    domain = Range(-oo, 0)
                else:
                    domain = Interval(-oo, 0, right_open=True)
            elif base.is_nonpositive:
                if base.is_integer:
                    domain = Range(-oo, 1)
                else:
                    domain = Interval(-oo, 0)
            elif base.is_nonnegative:
                if base.is_integer:
                    domain = Range(oo)
                else:
                    domain = Interval(0, oo)
            else:
                return
            
            return CartesianSpace(domain, *self.shape)


class Sliced(Expr):
    """Represents a mathematical object with Slices,
    in the form of x[start0:stop0, ..., start1:stop1]
    """
    is_symbol = True
    is_Atom = True

    base = property(lambda self: self.args[0])
    start = property(lambda self: self.args[1][0])
    stop = property(lambda self: self.args[1][1])
    indices = property(lambda self: self.args[1:])
    index = property(lambda self: self.args[1])

    def copy(self, **kwargs):
        return self.base.copy(**kwargs)[self.start:self.stop]

    @property
    def distribution(self):
        distribution = self.base.distribution
        if distribution is not None:
            return distribution
                         
        definition = self.definition
        if definition is not None: 
            if self.is_integer:
                from sympy.stats.drv_types import AbstractDiscreteDistribution
                return AbstractDiscreteDistribution(definition.function)
            else: 
                from sympy.stats.crv_types import AbstractContinuousDistribution
                return AbstractContinuousDistribution(definition) 

    @property
    def definition(self):
        return self.defun()

    @cacheit
    def defun(self):
        definition = self.base.defun()
        if definition is not None:
            try:
                return definition[self.indices]
            except:
                ...

    @property
    def domain_assumed(self):
        return self.base.domain_assumed

    @property
    def domain(self): 
        if self.dtype.is_set:
            return self.universalSet

        base = self.base
        domain = base.domain_assumed
        if domain is None:
            if self.is_integer:
                from sympy import Range
                domain = Range(**base.assumptions0)
            elif self.is_real:
                from sympy import Interval
                domain = Interval(**base.assumptions0)
            elif self.is_complex:
                domain = S.Complexes
            else:
                #todo:
                domain = S.Complexes

        shape = self.shape
        if not shape:
            return domain
        from sympy.sets.sets import CartesianSpace
        return CartesianSpace(domain, *shape)

    def _dummy_eq(self, other):
        return self == other

    def structurally_equal(self, other):
        if other.is_symbol:
            return self.shape == other.shape
        return False

# performing other.indices in self.indices
    def index_contains(self, other):
        if other.is_Indexed:
            if self.base != other.base: 
                return

            slices = self.indices
            _indices = other.indices
            if len(_indices) < len(slices):
                return
            
            return slices_contains_indices(slices, _indices)

        if other.is_Sliced:
            base = self.base
            _base = other.base
            if base == _base: 
                slices = self.indices
                _slices = other.indices
                if len(_slices) < len(slices):
                    return
        
                return slices_contains_slices(slices, _slices)
            
            elif _base.is_Indexed and _base.base == base:
                slices = self.indices
                _indices, _slices = other.indices_slices()
                
                if len(_indices) + len(_slices) < len(slices):
                    return
                
                if not slices_contains_indices(slices, _indices):
                    return
                
                if len(_indices) >= len(slices):
                    return True
                
                return slices_contains_slices(slices[len(_indices):], _slices)

        if other.is_SlicedIndexed:
            if self.base != other.base: 
                return
            
            slices = self.indices
            _slices, _indices = other.slices_indices
            if len(_slices) + len(_indices) < len(self.indices):
                return
    
            if not slices_contains_slices(slices, _slices):
                return
            
            if len(_slices) >= len(slices):
                return True
            
            return slices_contains_indices(slices, _indices)

    def index_complement(self, other):
        if not (other.is_Indexed or other.is_Sliced) or self.base != other.base: 
            return self
        
        if len(other.indices) != len(self.indices):
            return self

        indices = []
        from sympy import Range, FiniteSet
        if other.is_Sliced:
            indices = []
            for (start, stop), (_start, _stop) in zip(self.indices, other.indices):
                if start == _start and stop >= _stop:
                    indices.append(Range(_stop, stop))
                else:
                    indices.append(Range(start, stop) - Range(_start, _stop))
        else:
            indices = [Range(start, stop) - FiniteSet(index) for (start, stop), index in zip(self.indices, other.indices)]

        for i, index in enumerate(indices): 
            if index.is_Range:
                indices[i] = slice(index.start, index.stop)
            elif index.is_FiniteSet:
                indices[i] = next(iter(index))
            else:
                return self

        return self.base[tuple(indices)]

# performing indices intersection
    def index_intersect(self, other):
        if other.is_Indexed:
            if self.base != other.base: 
                return

            slices = self.indices
            _indices = other.indices
            if len(_indices) < len(slices):
                return
            
            if slices_contains_indices(slices, _indices):
                return other

            return

        if other.is_Sliced:
            base = self.base
            _base = other.base
            if base == _base: 
                slices = self.indices
                _slices = other.indices
                if len(_slices) >= len(slices):
                    if slices_contains_slices(slices, _slices):
                        return other
                else:
                    if slices_contains_slices(_slices, slices):
                        return self
            
            elif _base.is_Indexed and _base.base == base:
                slices = self.indices
                _indices, _slices = other.indices_slices()
                
                if len(_indices) + len(_slices) < len(slices):
                    return
                
                if not slices_contains_indices(slices, _indices):
                    return
                
                if len(_indices) >= len(slices):
                    return other
                
                if slices_contains_slices(slices[len(_indices):], _slices):
                    return other

        if other.is_SlicedIndexed:
            if self.base != other.base: 
                return
            
            slices = self.indices
            _slices, _indices = other.slices_indices
            if len(_slices) + len(_indices) < len(self.indices):
                return
    
            if not slices_contains_slices(slices, _slices):
                return
            
            if len(_slices) >= len(slices):
                return other
            
            if slices_contains_indices(slices, _indices):
                return other
        
    def cup_finiteset(self, var=None):
        from sympy.concrete.sets import Cup
        i = self.generate_var(integer=True, var=var)
        return Cup({self.base[i]}, (i, *self.index))

    @cacheit
    def __new__(cls, base, *indices, **kw_args):
        indices = [*indices]
        for i, index in enumerate(indices):
            start, stop, step = index.slice_args
            if start < 0:
                start = base.shape[i] + start
            else:
                start = sympify(start)
                    
            if stop < 0:
                stop = base.shape[i] + stop
            else: 
                stop = sympify(stop)
                
            if start == stop:
                raise Exception('empty slices')
            
            if step == 1:
                indices[i] = Tuple(start, stop)
            else:
                indices[i] = Tuple(start, stop, step)

        hit = None
        for i in range(len(indices) - 1, -1, -1):
            start, stop, step = indices[i].slice_args
            if stop == start + 1 and step == 1:
                indices[i] = start
                hit = i
            else:
                break
        
        if hit is not None:
            slices, indices = indices[:hit], indices[hit:]
            if slices:
                return SlicedIndexed(base, *slices, *indices)
            else:
                return base[indices]

        if isinstance(base, str):
            from sympy import oo
            base = Symbol(base, shape=(oo,))
        elif base.is_Symbol:
            assert base.shape
            if start.is_zero and stop == base.shape[len(indices) - 1]:
                indices = indices[:-1]
                if indices:
                    return base[indices]
                return base
            
            if indices[0].is_Tuple:
                start, stop, step = indices[0].slice_args
                if stop == start + 1:
                    base = base[start]
                    indices = indices[1:]
                    if indices:
                        return base[indices]
                    return base
                    
        elif not hasattr(base, '__getitem__') and not isinstance(base, Symbol):
            assert len(base.shape) >= len(indices)            
        elif base.is_Stack:
            if len(indices) == 1:
                [domain] = indices
                start, stop, step = domain.args
                if step == 1:
                    return base[start:stop]
                else:
                    return base[start:stop:step]
            else:
                start, stop = indices
                return base[start:stop]
            
        elif base.is_Exp:
            return base.func(Expr.__new__(cls, base.arg, *indices, **kw_args))
        
        elif base.is_Mul:
            return base[indices]
        
        elif base.is_Sliced:
            base, *slices = base.args
            for i, (_index, index) in enumerate(zip(slices, indices)):
                start, stop, step = index.slice_args
                _start, _stop, _step = _index.slice_args
                assert step == _step
                start += _start
                stop += _start
                if step != 1:
                    indices[i] = Tuple(start, stop, step)
                else:
                    indices[i] = Tuple(start, stop)
                
            indices += slices[len(indices):]
            return base[indices]
        
        return Expr.__new__(cls, base, *indices, **kw_args)

    def __iter__(self):
        raise TypeError

    @property
    def name(self):
        return str(self)

    @property
    def _diff_wrt(self):
        """Allow derivatives with respect to an ``Indexed`` object."""
        return True
    
    def get_parallel_slices(self, indices):
        [*self_indices] = self.indices[:len(indices)]
        for i, (self_index, index) in enumerate(zip(self_indices, indices)):
            self_start, self_stop, self_step = self_index.slice_args
            start, stop, step = index.slice_args
            start += self_start
            stop += self_start
            step = self_step
                
            self_indices[i] = Tuple(start, stop, step)
            
        return self_indices
            
    def get_parallel_indices(self, start, indices):
        [*self_indices] = self.indices[start: start + len(indices)]
        for i, (self_index, index) in enumerate(zip(self_indices, indices)):
            self_indices[i] = self_index[0] + index
            
        if len(indices) > len(self_indices):
            self_indices.extend(indices[len(self_indices):])
        return self_indices
    
    def __setitem__(self, indices, value):
        if isinstance(indices, tuple):
            if isinstance(indices[-1], slice):
                value, *slices = value.of(Sliced)
                
                size = len(slices)
                for i in range(size):
                    start, stop = slices[i].of(Tuple)
                    index = indices[i - size]
                    assert index.start == start
                    assert index.stop == stop
                    
                indices = indices[:-size]
                self[indices] = value
            else:
                args = value.of(Indexed)
                assert self == args[0]
                assert args[1:] == indices
        else:
            if isinstance(indices, slice):
                base, sliced = value.of(Sliced)
                start, stop = sliced.of(Tuple)
                assert indices.start == start
                assert indices.stop == stop
                
                assert self == base

            else:
                base, index = value.of(Indexed)
                assert self == base
                assert index == indices
    
    def __getitem__(self, indices, **kwargs):
        if (indices := self.simplify_indices(indices)) is None:
            return self
        
        if isinstance(indices, tuple):
            if len(self.indices) > len(indices):
                if not indices:
                    return self
                base = self.base
                for index, (start, stop, *step) in zip(indices, self.indices):
                    if step:
                        [step] = step
                        index *= step
                    base = base[start + index]
                    
                return self.func(base, *self.indices[len(indices):])
            else:
                
                for pivot, index in enumerate(indices):
                    if not isinstance(index, Tuple):
                        break
                else:
                    pivot += 1

                # former must be a tuple of slices;
                former = indices[:pivot]
                if len(former) > len(self.indices):
                    former, latter = former[:len(self.indices)], former[len(self.indices):]
                    former = self.get_parallel_slices(former)
                    former += latter
                else:
                    former = self.get_parallel_slices(former)

                latter = indices[pivot:]
                # latter could be a tuple of both slices and indices, but starting with indices
                if latter:
                    if len(former) < len(self.indices):
                        latter = self.get_parallel_indices(len(former), latter)
                        
                    slices = former
                    for pivot, index in enumerate(latter):
                        if isinstance(index, Tuple):
                            break
                    else:
                        pivot += 1
                        
                    former, latter = latter[:pivot], latter[pivot:]
                    
                    if slices:
                        indexed = SlicedIndexed(self.base, *slices, *former)
                    else:
                        indexed = self.base[tuple(former)]
                        
                    if latter:
                        return indexed[tuple(latter)]
                    else:
                        return indexed
                    
                return self.func(self.base, *former)
                
        elif isinstance(indices, Tuple):
            start, stop, step = indices.slice_args
            if start is None:
                start = 0
                                
            if stop is None:
                stop = self.shape[0]
                
            if start == stop - 1:
                return self[start]
            
            base, index, *indices = self.args
            self_start, self_stop, self_step = index.slice_args
            if self_step == 1:
                start, stop = self_start + start, self_start + stop
                return base[(slice(start, stop), *indices)]

            elif step == 1:
                step = self_step
                start = self_start + start * step
                stop = self_start + stop * step
                
                size = (stop - start) / step
                if size.is_Ceil:
                    stop = size.arg * step + start
                    
                return base[(slice(start, stop, step), *indices)]
            else:
                raise "unimplemented cases"
        else:
            (start, stop, *step), *slices = self.indices
            if step:
                step, = step
                indices *= step

            return self.base[tuple([indices + start] + slices)]

    def _eval_derivative(self, wrt):
        from sympy.tensor.array.ndim_array import NDimArray
        from sympy.functions.special.tensor_functions import KroneckerDelta
        
        if isinstance(wrt, Indexed) and wrt.base == self.base:
            if len(self.indices) != len(wrt.indices):
                msg = "Different # of indices: d({!s})/d({!s})".format(self,
                                                                       wrt)
                raise IndexException(msg)
            result = S.One
            for index1, index2 in zip(self.indices, wrt.indices):
                result *= KroneckerDelta(index1, index2)
            return result
        elif isinstance(self.base, NDimArray):
            from sympy.tensor.array import derive_by_array
            return Indexed(derive_by_array(self.base, wrt), *self.args[1:])
        else:
            if Tuple(self.indices).has(wrt):
                return S.NaN
            return S.Zero

    @property
    def rank(self):
        """
        Returns the rank of the ``Indexed`` object.

        Examples
        ========

        >>> from sympy import Indexed, Idx, symbols
        >>> i, j, k, l, m = symbols('i:m', cls=Idx)
        >>> Indexed('A', i, j).rank
        2
        >>> q = Indexed('A', i, j, k, l, m)
        >>> q.rank
        5
        >>> q.rank == len(q.indices)
        True

        """
        return len(self.args) - 1

    @cacheit
    def _eval_shape(self):
        sizes = []
        from sympy.functions.elementary.integers import Ceil
        for index in self.indices:
            start, stop, step = index.slice_args
            if step is None:
                step = S.One
            sizes.append(Ceil((stop - start) / step))
                
        if len(self.base.shape) > len(sizes):
            sizes += [self.base.shape[i] for i in range(len(sizes), len(self.base.shape))]

        return tuple(sizes)

    @property
    def ranges(self):
        """Returns a list of tuples with lower and upper range of each index.

        If an index does not define the data members upper and lower, the
        corresponding slot in the list contains ``None`` instead of a tuple.

        Examples
        ========

        >>> from sympy import Indexed,Idx, symbols
        >>> Indexed('A', Idx('i', 2), Idx('j', 4), Idx('k', 8)).ranges
        [(0, 1), (0, 3), (0, 7)]
        >>> Indexed('A', Idx('i', 3), Idx('j', 3), Idx('k', 3)).ranges
        [(0, 2), (0, 2), (0, 2)]
        >>> x, y, z = symbols('x y z', integer=True)
        >>> Indexed('A', x, y, z).ranges
        [None, None, None]

        """
        ranges = []
        for i in self.indices:
            sentinel = object()
            upper = getattr(i, 'upper', sentinel)
            lower = getattr(i, 'lower', sentinel)
            if sentinel not in (upper, lower):
                ranges.append(Tuple(lower, upper))
            else:
                ranges.append(None)
        return ranges

    def index_generator(self, p):
        base_shape = self.base.shape
        for i, index in enumerate(self.indices):
            start, stop, step = index.slice_args

            if start.is_zero:
                start = ''
            else:
                start = p._print(start)
                
            if stop == base_shape[i]:
                stop = ''
            else:
                stop = p._print(stop)

            if step == 1:                
                yield ':'.join([start, stop])
            else:
                yield ':'.join([start, stop, p._print(step)])

    def _sympystr(self, p):
        base = self.base
        if base.is_Indexed:
            base, *indices = base.args
            indices = [p._print(index) for index in indices] + [*self.index_generator(p)]
        else:
            indices = self.index_generator(p)            
        return "%s[%s]" % (p._print(base), ', '.join(indices))

    def _lean(self, p):
        base = self.base
        if base.is_Indexed:
            base, *indices = base.args
            indices = [p._print(index) for index in indices] + [*self.index_generator(p)]
        else:
            indices = self.index_generator(p)            
        return "%s[%s]" % (p._print(base), ', '.join(indices))

    def _latex(self, p, **kwargs):
        base = self.base
        exp = None
        import re
        if base.is_Indexed:
            if base.base.is_Symbol:
                if m := re.match(r"(\w+)\^([\w-]+)", base.base.name):
                    tex_base, exp = m.groups()
                
            indices = [p._print(index) for index in base.indices]
            indices += [*self.index_generator(p)]
            if exp is None:
                tex = '{%s}_{%s}' % (base.base._latex(p, **kwargs), ', '.join(indices))
            else:
                tex = '{%s}_{%s}^{%s}' % (tex_base, ', '.join(indices), exp)
        else:
            if base.is_Symbol:
                if m := re.match(r"(\w+)\^([\w-]+)", base.name):
                    tex_base, exp = m.groups()

            if exp is None:
                tex_base = base._latex(p, **kwargs)
                tex = '{%s}_{%s}' % (tex_base, ', '.join(self.index_generator(p)))
            else:
                tex = '{%s}_{%s}^{%s}' % (tex_base, ', '.join(self.index_generator(p)), exp)
                
        return tex

    @cacheit
    def _eval_free_symbols(self):
        base_free_symbols = self.base.free_symbols
        indices_free_symbols = {fs for i in self.indices for fs in i.free_symbols}
        if base_free_symbols:
            return {self} | base_free_symbols | indices_free_symbols
        else:
            return indices_free_symbols

    @property
    def expr_free_symbols(self):
        return {self}

    # return expr._has(self)
    def has_match(self, expr):
        from sympy import Unequal
        if expr.is_Indexed:
            if expr.base == self.base:
                for _index, index in zip(expr.indices, self.indices):
                    start, stop, step = index.slice_args
                    if _index < start or _index >= stop:
                        return False
# it is possible for them to be equal!
                return True

            if self.base.is_Indexed and self.base.base == expr.base:
                #self is a Indexed Sliced object
                base, *slices = self.args
                base, *indices = base.args
                _indices = expr.indices
                for _index, index in zip(_indices, indices):
                    if Unequal(_index, index):
                        return False
                    
                for _index, index in zip(_indices[len(indices):], slices):
                    start, stop, step = index.slice_args
                    if _index < start or _index >= stop:
                        return False
# it is possible for them to be equal!
                return True
                
        if expr.is_Sliced:
            if expr.base == self.base:
                for _index, index in zip(expr.indices, self.indices):
                    index_start, index_stop, index_step = _index.slice_args
                    start, stop, step = index.slice_args
                    if index_stop <= start or index_start >= stop:
                        return False
    # it is still possible for them to be equal!
                return True

            if expr.base.is_Indexed and expr.base.base == self.base:
                _indices = expr.base.indices
                _slices = expr.indices
                slices = self.indices
                for _index, index in zip(_indices, slices):
                    start, stop, step = index.slice_args
                    if _index < start or _index >= stop:
                        return False

                for _index, index in zip(_slices, slices[len(_indices):]):
                    start, stop, step = index.slice_args
                    _start, _stop, _step = _index.slice_args
                    if _stop <= start or _start >= stop:
                        return False
    # it is still possible for them to be equal!
                return True
            
            if self.base.is_Indexed and self.base.base == expr.base:
                _slices = expr.indices
                base, *slices = self.args
                indices = base.indices
                for _index, index in zip(_slices, indices):
                    _start, _stop, _step = _index.slice_args
                    if index < _start or index >= _stop:
                        return False

                for _index, index in zip(_slices[len(indices):], slices):
                    start, stop, step = index.slice_args
                    _start, _stop, _step = _index.slice_args
                    if _stop <= start or _start >= stop:
                        return False
    # it is still possible for them to be equal!
                return True

            base = expr.base.definition
            if base is not None and base._has(self):
                return True
        return False

    def _has_matcher(self):
        """Helper for .has()"""
        return self.match
    
    @cacheit
    def _has(self, pattern):
        """Helper for .has()"""
        from sympy.core.function import UndefinedFunction, Function
        if isinstance(pattern, UndefinedFunction):
            return any(f.func == pattern or f == pattern for f in self.atoms(Function, UndefinedFunction))

        pattern = sympify(pattern)
        from sympy.core.core import BasicMeta
        from sympy import preorder_traversal
        
        if isinstance(pattern, BasicMeta):
            return any(isinstance(arg, pattern) for arg in preorder_traversal(self))

        has_match = getattr(pattern, 'has_match', None)
        if has_match is not None:
            if has_match(self):
                return True
            elif pattern.is_Indexed:
                return False
            
            args = self.args[1:]
        else:
            if self == pattern:
                return True
            args = self.args

        if any(arg._has(pattern) for arg in args):
            return True
        
        if self.base.is_AppliedUndef:
            return any(arg._has(pattern) for arg in self.base.args)

        if self.base.is_Indexed:
            if self.base._has(pattern):
                return True
        
        definition = self.base.defun()
        if definition is not None: 
            if any(index._has(pattern) for index in self.indices):
                return True
            
            return definition._has(pattern)
        return False

    @property
    def dtype(self):
        return self.base.dtype

    def _eval_is_extended_integer(self):
        return self.base.is_extended_integer

    def _eval_is_extended_real(self):
        return self.base.is_extended_real

    def _eval_is_hyper_real(self):
        return self.base.is_hyper_real

    def _eval_is_super_real(self):
        return self.base.is_super_real
    
    def _eval_is_extended_complex(self):
        return self.base.is_extended_complex

    def _eval_is_extended_negative(self):
        return self.base.is_extended_negative

    def _eval_is_extended_positive(self):
        return self.base.is_extended_positive

    def _eval_is_finite(self):
        return self.base.is_finite

    def _eval_is_zero(self):
        return self.base.is_zero

    def _eval_is_random(self):
        return any(arg.is_random for arg in self.args)
    
    @property
    def is_given(self): 
        return self.base.is_given

    as_boolean = Symbol.as_boolean

    @cacheit
    def _eval_domain_defined(self, x, allow_empty=False, **_):
        domain = self.base.domain_defined(x)
        start, stop, step = self.index.slice_args
            
        if allow_empty:
            domain &= x.domain_conditioned(stop - start >= 0)
        else:
            domain &= x.domain_conditioned(stop - start > 0)
        return domain

    def domain_definition(self, allow_empty=None):
        base = self.base
        
        from sympy.logic.boolalg import And
        eqs = []
        for i, sliced in enumerate(self.indices):
            start, stop, step = sliced.slice_args
            size = base.shape[i]
            eqs += [start >= 0, start <= stop if allow_empty else start < stop, stop <= size, step >= 0]
            
        return And(*eqs) 

    @property
    def T(self):
        if len(self.shape) < 2:
            return self
        return super(Sliced, self).T

    def _subs(self, old, new, **kwargs):
        if self == old:
            return new
        if self.base == old:
            return new[tuple(slice(*index) for index in self.indices)]

        return Expr._subs(self, old, new, **kwargs)
    
    def _subs_sliced(self, old, new, **hints):
        if self.base == old.base and len(self.indices) >= len(old.indices):
# let us suppose that:
# base[      self_start : self_stop]       = self
# 
# base[start            :            stop] = old
# 
# new = old
# 
# base[self_start] = base[start:stop][self_start - start] = old[self_start - start] = new[self_start - start]
# base[self_start + 1] = base[start:stop][self_start - start + 1] = old[self_start - start + 1] = new[self_start - start + 1]
# base[self_stop - 1] = base[start:stop][self_stop - 1 - start] = old[self_stop - 1 - start] = new[self_stop - 1 - start]
# 
# new[self_start - start: self_stop - start]
            self_indices = self.indices
            old_indices = old.indices
            
            if len(self_indices) > len(old_indices):
                shape = self.base.shape
                old_indices = [*old_indices]
                while len(self_indices) > len(old_indices): 
                    old_indices.append(Tuple(0, shape[len(old_indices)]))                                                  
#             elif len(self_indices) < len(old_indices):            
#                 shape = self.base.shape
#                 self_indices = [*self_indices]
#                 while len(self_indices) < len(old_indices): 
#                     self_indices.append((0, len(self_indices)))
                                    
            indices = []
            
            from sympy.functions.elementary.integers import Ceil
            for self_index, index in zip(self_indices, old_indices):
                self_start, self_stop, self_step = self_index.slice_args
                start, stop, step = index.slice_args
                if self_step == step and start <= self_start and stop >= self_stop:
                    if step == 1:
                        indices.append(slice(self_start - start, self_stop - start))
                    else:
                        indices.append(slice(Ceil((self_start - start) / step), Ceil((self_stop - start) / step)))
                else: 
                    break

            else:
                return new[indices]
            
        return Expr._subs_sliced(self, old, new, **hints)
    
    def detect_indexed(self, function):
        indexed = set()
        for expr in function.preorder_traversal():
            if expr.is_Indexed and expr.base == self.base:
                indexed.add(expr)
        return indexed
                
    @property
    def domain_bounded(self):
        base = self.base
        if base.is_Symbol: 
            from sympy import CartesianSpace
            from sympy import Interval, oo, Range
            if 'domain' in base._assumptions:
                domain = base._assumptions['domain']
            elif base.is_positive:
                if base.is_integer:
                    domain = Range(1, oo)
                else:
                    domain = Interval(0, oo, left_open=True)
            elif base.is_negative:
                if base.is_integer:
                    domain = Range(-oo, 0)
                else:
                    domain = Interval(-oo, 0, right_open=True)
            elif base.is_nonpositive:
                if base.is_integer:
                    domain = Range(-oo, 1)
                else:
                    domain = Interval(-oo, 0)
            elif base.is_nonnegative:
                if base.is_integer:
                    domain = Range(oo)
                else:
                    domain = Interval(0, oo)
            else:
                return
            
            return CartesianSpace(domain, *self.shape)

    @property
    def is_bounded(self):
        self = self.base
        if self.is_Symbol:
            return self._eval_is_bounded()

    @property
    def unbounded(self):
        if self.is_bounded:
            return self.copy(domain=None)
        return self

    def expand_indices(self, limits, expr=None):
        base, *indices = self.args
        if base.is_Indexed:
            base = base.expand_indices(limits)
            if base.is_Sliced:
                base, *new_indices = base.args
                indices = new_indices + indices
                return Sliced(base, *indices)
            return self
        
        indices_transformed = [*indices]
        hit = False
        for limit in limits:
            i, *ab = limit
            if not i.is_integer:
                continue

            if len(ab) == 2 and not ab[1].is_set:
                if args := expand_indices(limit, indices):
                    t, args = args
                    indices_transformed[t] = args
                    hit = True

            elif not ab and expr is not None:
                domain = expr.domain_defined(i)
                if domain.is_Range:
                    if args := expand_indices((i, *domain.args), indices):
                        t, args = args
                        indices_transformed[t] = args
                        hit = True
                
        if hit:
            return base[tuple(indices_transformed)]
        
        return self

    
    @staticmethod
    def simplify_Lamda(self, squeeze=False):
        (var, *ab), *limits = self.limits
        base, *slices = self.expr.args
        if base.is_Indexed:
            base, *indices = base.args
            diff = indices[-1] - var
            if not diff._has(var):
                if len(indices) > 1:
                    ...
                else:
                    if len(ab) == 2:
                        a, b = ab
                        if b.is_integer:
                            if not limits:
                                if not any(s._has(var) for s in slices):
                                    return Sliced(base, Tuple(a + diff, b + diff), *slices)
            
        return self
    
    @property
    def var(self):
        assert self.base.is_random
        assert not any(index.is_random for index in self.indices)
        return self.base.var[self.indices]
    
    @property
    def surrogate(self):
        assert self.base.is_random
        assert not any(index.is_random for index in self.indices)
        return self.base.surrogate[self.indices]

    def __and__(self, other):
        """Overloading for & operator"""
        if self.is_random and other.is_random:
            if not other.is_bool:
                other = other.as_boolean()
            return self.as_boolean() & other
        
        return super(Sliced, self).__and__(other)

    def catch_exception(self, old, new):
        base, *slices = self.args
        for a, b in slices:
            if a._subs(old, new) == b._subs(old, new):
                return True

    def indices_slices(self):
        base, *slices = self.args
        return base.indices, slices

    def indexOf(self, indexed):
        if indexed.is_Indexed:
            if indexed.base == self.base:
                indices = indexed.indices
                slices = self.indices
                if len(indices) < len(slices):
                    indices = (i - start for i, (start, stop) in zip(indices, slices[:len(indices)]))
                    return tuple(indices) + slices[len(indices):]
                
                elif len(indices) > len(slices):
                    indices_former = (i - start for i, (start, stop) in zip(indices[:len(slices)], slices))
                    return tuple(indices_former) + indices[len(slices):]
                
                else:
                    indices = (i - start for i, (start, stop) in zip(indices, slices))
                    return tuple(indices)
                

class SlicedIndexed(Expr):
    """Represents a mathematical object with Slices and indices both.
    in the form of x[start0:stop0, ..., start1:stop1, index0,..., index1]

    """
    is_symbol = True
    is_Atom = True

    base = property(lambda self: self.args[0])
    start = property(lambda self: self.args[1])
    stop = property(lambda self: self.args[2])

    def slices_indices(self):
        indices = self.args[1:]
        for i, arg in enumerate(indices):
            if arg.is_Tuple:
                continue
            break
        else:
            raise Exception('SliceIndexed requires at least one index')
        
        return indices[:i], indices[i:]
    
    @property
    def slices(self):
        return self.slices_indices()[0]
     
    @property
    def indices(self):
        return self.slices_indices()[1]
    
    def copy(self, **kwargs):
        return self.base.copy(**kwargs)[self.start:self.stop]

    @property
    def distribution(self):
        distribution = self.base.distribution
        if distribution is not None:
            return distribution
                         
        definition = self.definition
        if definition is not None: 
            if self.is_integer:
                from sympy.stats.drv_types import AbstractDiscreteDistribution
                return AbstractDiscreteDistribution(definition.function)
            else: 
                from sympy.stats.crv_types import AbstractContinuousDistribution
                return AbstractContinuousDistribution(definition) 

    @property
    def definition(self):
        return self.defun()

    @cacheit
    def defun(self):
        definition = self.base.defun()
        if definition is not None:
            try:
                return definition[self.indices]
            except:
                ...
        
    @property
    def domain_assumed(self):
        return self.base.domain_assumed

    @property
    def domain(self): 
        if self.dtype.is_set:
            return self.universalSet

        from sympy import Interval, Range, CartesianSpace
        domain = self.base.domain_assumed
        if domain is None:
            assumptions = self.base.assumptions0
            integer = assumptions.pop('integer', self.base.is_integer)
            domain = (Range if integer else Interval)(**assumptions)

        shape = self.shape
        if not shape:
            return domain
        return CartesianSpace(domain, *shape)

    def _dummy_eq(self, other):
        return self == other

    def structurally_equal(self, other):
        if other.is_symbol:
            return self.shape == other.shape
        return False

    # performing other in self
    def index_contains(self, other):
        if other.is_Indexed:
            if self.base != other.base: 
                return
            
            slices, indices = self.slices_indices()
            _indices = other.indices
            if len(_indices) < len(slices) + len(indices):
                return
    
            if not slices_contains_indices(slices, _indices):
                return
            
            return indices_contains_indices(indices, _indices)

        if other.is_Sliced:
            base = self.base
            _base = other.base
            if base == _base:
                return

            elif _base.is_Indexed and _base.base == base:
                slices, indices = self.slices_indices()
                _indices = _base.indices
                
                if len(_indices) <= len(slices):
                    return
                
                if not slices_contains_indices(slices, _indices):
                    return
                
                return indices_contains_indices(indices, _indices[len(slices):])

        if other.is_SlicedIndexed:
            if self.base != other.base: 
                return
            
            slices, indices = self.slices_indices()
            _slices, _indices = other.slices_indices()
            if len(_slices) > len(slices):
                return
            
            if not slices_contains_slices(slices, _slices):
                return
            
            if len(_slices) + len(_indices) < len(slices) + len(indices):
                return
                
            if len(_slices) < len(slices):
                if not slices_contains_indices(slices[len(_slices):], indices):
                    return
            
                return indices_contains_indices(indices, _indices[len(slices) - len(_slices):])
            else:
                return indices_contains_indices(indices, _indices)

    # performing other in self
    def index_intersect(self, other):
        if other.is_Indexed:
            if self.base != other.base: 
                return
            
            slices, indices = self.slices_indices()
            _indices = other.indices
            if len(_indices) < len(slices) + len(indices):
                return
    
            if not slices_contains_indices(slices, _indices):
                return
            
            if indices_contains_indices(indices, _indices):
                return other

        if other.is_Sliced:
            base = self.base
            _base = other.base
            if base == _base:
                return

            elif _base.is_Indexed and _base.base == base:
                slices, indices = self.slices_indices()
                _indices = _base.indices
                
                if len(_indices) <= len(slices):
                    return
                
                if not slices_contains_indices(slices, _indices):
                    return
                
                if indices_contains_indices(indices, _indices[len(slices):]):
                    return other

        if other.is_SlicedIndexed:
            if self.base != other.base: 
                return
            
            slices, indices = self.slices_indices()
            _slices, _indices = other.slices_indices()
            if len(_slices) > len(slices):
                return
            
            if not slices_contains_slices(slices, _slices):
                return
            
            if len(_slices) + len(_indices) < len(slices) + len(indices):
                return
                
            if len(_slices) < len(slices):
                if not slices_contains_indices(slices[len(_slices):], indices):
                    return
            
                if indices_contains_indices(indices, _indices[len(slices) - len(_slices):]):
                    return other
            else:
                if indices_contains_indices(indices, _indices):
                    return other

    # performing indices complement
    def index_complement(self, other):
        if other.is_Indexed:
            if self.base != other.base: 
                return self
            
            slices, indices = self.slices_indices()
            _indices = other.indices
            if len(_indices) < len(slices) + len(indices):
                return self
    
            if not slices_contains_indices(slices, _indices):
                return self
            
            if indices_contains_indices(indices, _indices):
                return
            return self

        if other.is_Sliced:
            base = self.base
            _base = other.base
            if base == _base:
                return self

            elif _base.is_Indexed and _base.base == base:
                slices, indices = self.slices_indices()
                _indices = _base.indices
                
                if len(_indices) <= len(slices):
                    return self
                
                if not slices_contains_indices(slices, _indices):
                    return self
                
                if indices_contains_indices(indices, _indices[len(slices):]):
                    return
                return self
            
        if other.is_SlicedIndexed:
            if self.base != other.base: 
                return self
            
            slices, indices = self.slices_indices()
            _slices, _indices = other.slices_indices()
            if len(_slices) > len(slices):
                return self
            
            if not slices_contains_slices(slices, _slices):
                return self
            
            if len(_slices) + len(_indices) < len(slices) + len(indices):
                return self
                
            if len(_slices) < len(slices):
                if not slices_contains_indices(slices[len(_slices):], indices):
                    return self
            
                if indices_contains_indices(indices, _indices[len(slices) - len(_slices):]):
                    return
            else:
                if indices_contains_indices(indices, _indices):
                    return
                
            return self

    def cup_finiteset(self, var=None):
        from sympy.concrete.sets import Cup

        i = self.generate_var(integer=True, var=var)
        return Cup({self.base[i]}, (i, *self.index))

    @cacheit
    def __new__(cls, base, *args, **kw_args):
        assert len(args) >= 2, "SlicedIndexed needs at least two indices."
        indices = []
        positionOfSlices = []
        positionOfIndices = []
        for i, arg in enumerate(args):
            if isinstance(arg, Tuple):
                start, stop, step = arg.slice_args
                if start is None:
                    start = 0
                    
                if stop is None:
                    stop = base.shape[i]
                    
                if step is None:
                    step = 1
                    
                if step == 1:
                    if stop == start + 1:
                        indices.append(start)
                        positionOfIndices.append(i)
                        continue
                    indices.append(Tuple(start, stop))
                else:
                    indices.append(Tuple(start, stop, step))
                positionOfSlices.append(i)
            else:
                arg = sympify(arg)
                if arg.is_Tuple:
                    positionOfSlices.append(i)
                else:
                    positionOfIndices.append(i)
                indices.append(arg)

        if not positionOfSlices:
            return base[indices]

        assert positionOfSlices == [*range(0, len(positionOfSlices))], 'SliceIndexed requires nonempty continuous slices from the begining'
        assert positionOfIndices and positionOfIndices == [*range(len(positionOfSlices), len(args))], 'SliceIndexed requires nonempty continuous indices up to the end'
        args = indices

        if isinstance(base, str):
            from sympy import oo
            base = Symbol(base, shape=(oo,))
        elif base.is_Symbol:
            assert len(base.shape) >= 2
        elif not hasattr(base, '__getitem__') and not isinstance(base, Symbol):
            raise TypeError("""Indexed expects string, Symbol, or IndexedBase as base.""")
        elif base.is_Stack:
            start, stop = args
            assert start != stop
            return base[start: stop]
            
        return Expr.__new__(cls, base, *args, **kw_args)

    def __iter__(self):
        raise TypeError

    @property
    def name(self):
        return str(self)

    @property
    def _diff_wrt(self):
        """Allow derivatives with respect to an ``Indexed`` object."""
        return True

    def __getitem__(self, indices):
        if (indices := self.simplify_indices(indices)) is None:
            return self
        
        if isinstance(indices, tuple):
            slices, _indices = self.slices_indices()
            
            iteration = min(len(slices), len(indices))
                
            slices_keys = []
            for i in range(iteration):
                index = indices[i]
                start, stop = slices[i]
                if isinstance(index, Tuple):
                    _start, _stop, _step = index.slice_args

                    if _start is None:
                        _start = S.Zero
                        
                    if _stop is None:
                        _stop = self.base.shape[i]
                        
                    if _step is None:
                        _step = S.One
                    
                    _start -= start
                    _stop -= start
                    slices_keys.append(slice(_start, _stop, _step))
                else:
                    slices_keys.append(index + start)
                    
            slices_keys = tuple(slices_keys) + slices[len(indices):] + _indices
            if iteration < len(indices):
                slices_keys += indices[iteration:]
                
            return self.base[slices_keys]
            
        elif isinstance(indices, Tuple):
            start, stop, step = indices.slice_args
            if start is None:
                start = 0
                
            if start == stop - 1:
                return self[start]
            
            if step is None:
                step = S.One
                
            base, index, *indices = self.args
            self_start, self_stop = index
            start, stop = self_start + start, self_start + stop
#             assert stop <= self_stop, "try to prove, %s <= %s" % (stop, self_stop)
            return self.base[(slice(start, stop, step), *indices)]
        
        else:
            first, *slices = self.slices
            start, stop, step = first.slice_args
            if step is None:
                step = S.One
                
            base = self.base[indices * step + start]
            if slices:
                return self.func(base, *slices, *self.indices)
            return base[self.indices]

    def _eval_derivative(self, wrt):
        from sympy.tensor.array.ndim_array import NDimArray
        from sympy.functions.special.tensor_functions import KroneckerDelta
        
        if isinstance(wrt, Indexed) and wrt.base == self.base:
            if len(self.indices) != len(wrt.indices):
                msg = "Different # of indices: d({!s})/d({!s})".format(self,
                                                                       wrt)
                raise IndexException(msg)
            result = S.One
            for index1, index2 in zip(self.indices, wrt.indices):
                result *= KroneckerDelta(index1, index2)
            return result
        elif isinstance(self.base, NDimArray):
            from sympy.tensor.array import derive_by_array
            return Indexed(derive_by_array(self.base, wrt), *self.args[1:])
        else:
            if Tuple(self.indices).has(wrt):
                return S.NaN
            return S.Zero

    @property
    def rank(self):
        """
        Returns the rank of the ``Indexed`` object.

        Examples
        ========

        >>> from sympy import Indexed, Idx, symbols
        >>> i, j, k, l, m = symbols('i:m', cls=Idx)
        >>> Indexed('A', i, j).rank
        2
        >>> q = Indexed('A', i, j, k, l, m)
        >>> q.rank
        5
        >>> q.rank == len(q.indices)
        True

        """
        return len(self.args) - 1

    @cacheit
    def _eval_shape(self):
        from sympy.functions.elementary.integers import Ceil
        sizes = []
        for index in self.slices:
            start, stop, step = index.slice_args
            if step is None:
                sizes.append(stop - start)
            else:
                sizes.append(Ceil((stop - start) / step))
        
        sizes = tuple(sizes)
        numOfIndices = len(self.args) - 1
        base_length = len(self.base.shape)
        if base_length > numOfIndices: 
            sizes += self.base.shape[numOfIndices:]

        return sizes

    @property
    def ranges(self):
        """Returns a list of tuples with lower and upper range of each index.

        If an index does not define the data members upper and lower, the
        corresponding slot in the list contains ``None`` instead of a tuple.

        Examples
        ========

        >>> from sympy import Indexed,Idx, symbols
        >>> Indexed('A', Idx('i', 2), Idx('j', 4), Idx('k', 8)).ranges
        [(0, 1), (0, 3), (0, 7)]
        >>> Indexed('A', Idx('i', 3), Idx('j', 3), Idx('k', 3)).ranges
        [(0, 2), (0, 2), (0, 2)]
        >>> x, y, z = symbols('x y z', integer=True)
        >>> Indexed('A', x, y, z).ranges
        [None, None, None]

        """
        ranges = []
        for i in self.indices:
            sentinel = object()
            upper = getattr(i, 'upper', sentinel)
            lower = getattr(i, 'lower', sentinel)
            if sentinel not in (upper, lower):
                ranges.append(Tuple(lower, upper))
            else:
                ranges.append(None)
        return ranges

    def _sympystr(self, p):
        slices, indices = self.slices_indices()
        
        args = []
        for i, s in enumerate(slices):
            start, stop, step = s.slice_args
            if start.is_zero:
                start = ''
            else:
                start = p._print(start)
            
            if stop == self.base.shape[i]:
                stop = ''
            else: 
                stop = p._print(stop)
            
            if step == 1:                    
                args.append('%s:%s' % (start, stop))
            else:
                step = p._print(step)
                args.append('%s:%s:%s' % (start, stop, step))
            
        args += [p._print(i) for i in indices]
            
        base = self.base
        if base.is_Indexed: 
            args = [p._print(index) for index in base.indices] + args
            base = base.base
            
        return "%s[%s]" % (p._print(base), ', '.join(args))

    def _lean(self, p):
        slices, indices = self.slices_indices()
        
        args = []
        for i, s in enumerate(slices):
            start, stop, step = s.slice_args
            if start.is_zero:
                start = ''
            else:
                start = p._print(start)
            
            if stop == self.base.shape[i]:
                stop = ''
            else: 
                stop = p._print(stop)
            
            if step == 1:                    
                args.append('%s:%s' % (start, stop))
            else:
                step = p._print(step)
                args.append('%s:%s:%s' % (start, stop, step))
            
        args += [p._print(i) for i in indices]
            
        base = self.base
        if base.is_Indexed: 
            args = [p._print(index) for index in base.indices] + args
            base = base.base
            
        return "%s[%s]" % (p._print(base), ', '.join(args))

    def _latex(self, p, **kwargs):
        slices, indices = self.slices_indices()
        
        args = []
        for i, s in enumerate(slices):
            start, stop, step = s.slice_args
            if start.is_zero:
                start = ''
            else:
                start = p._print(start)
            
            if stop == self.base.shape[i]:
                stop = ''
            else: 
                stop = p._print(stop)
                
            if step == 1:
                args.append('%s:%s' % (start, stop))
            else:
                step = p._print(step)
                args.append('%s:%s:%s' % (start, stop, step))
            
        args += [p._print(i) for i in indices]
        
        base = self.base
        if base.is_Indexed: 
            args = [p._print(index) for index in base.indices] + args
            base = base.base
            
        return "{%s}_{%s}" % (base._latex(p, **kwargs), ','.join(args))

    @cacheit
    def _eval_free_symbols(self):
        indices_free_symbols = {fs for i in self.args for fs in i.free_symbols}
        if self.base.is_Symbol:
            return {self} | indices_free_symbols
        else:
            return indices_free_symbols

    @property
    def expr_free_symbols(self):
        return {self}

    # return expr._has(self)
    def has_match(self, expr):
        if expr.is_Indexed and expr.base == self.base:
            from sympy import Unequal
            _indices = expr.indices
            slices, indices = self.slices_indices()
            
            for _index, (start, stop) in zip(_indices, slices):
                if _index < start or _index >= stop:
                    return False
            
            for _index, index in zip(_indices[len(slices):], indices):
                if Unequal(_index, index):
                    return False
            
# it is possible for them to be equal!
            return True
        if expr.is_Sliced:
            if expr.base == self.base:
                _slices = expr.indices
                slices, indices = self.slices_indices()

                for (_start, _stop), (start, stop) in zip(_slices, slices):
                    if _stop <= start or _start >= stop:
                        return False
                
                for (_start, _stop), index in zip(_slices[len(slices):], indices):
                    if _stop <= index or _start > index:
                        return False
                
    # it is still possible for them to be equal!
                return True
            else:
                if expr.base.is_AppliedUndef:
                    return any(arg._has(self) for arg in expr.base.args)
                base = expr.base.defun()
                if base is not None and base._has(self):
                    return True
        return False

    def _has_matcher(self):
        """Helper for .has()"""
        return self.match

    @cacheit
    def _has(self, pattern):
        """Helper for .has()"""
        from sympy.core.function import UndefinedFunction, Function
        if isinstance(pattern, UndefinedFunction):
            return any(f.func == pattern or f == pattern for f in self.atoms(Function, UndefinedFunction))

        pattern = sympify(pattern)
        from sympy.core.core import BasicMeta
        from sympy import preorder_traversal
        
        if isinstance(pattern, BasicMeta):
            return any(isinstance(arg, pattern) for arg in preorder_traversal(self))

        has_match = getattr(pattern, 'has_match', None)
        if has_match is not None: 
            if has_match(self):
                return True
            args = self.args[1:]
        else:
            if self == pattern:
                return True
            args = self.args

        if any(arg._has(pattern) for arg in args):
            return True
        
        definition = self.base.definition
        if definition is not None: 
            return definition._has(pattern)
        
        return False

    @property
    def dtype(self):
        return self.base.dtype

    def _eval_is_extended_integer(self):
        return self.base.is_extended_integer

    def _eval_is_extended_real(self):
        return self.base.is_extended_real

    def _eval_is_hyper_real(self):
        return self.base.is_hyper_real

    def _eval_is_super_real(self):
        return self.base.is_super_real

    def _eval_is_extended_complex(self):
        return self.base.is_extended_complex

    def _eval_is_extended_negative(self):
        return self.base.is_extended_negative

    def _eval_is_extended_positive(self):
        return self.base.is_extended_positive

    def _eval_is_finite(self):
        return self.base.is_finite

    def _eval_is_zero(self):
        return self.base.is_zero

    def _eval_is_random(self):
        return any(arg.is_random for arg in self.args)
    
    @property
    def is_given(self): 
        return self.base.is_given

    as_boolean = Symbol.as_boolean

    @cacheit
    def _eval_domain_defined(self, x, allow_empty=False, **_):
        domain = self.base.domain_defined(x)
        for s in self.slices:
            start, stop = s
            if allow_empty:
                domain &= x.domain_conditioned(start <= stop)
            else:
                domain &= x.domain_conditioned(start < stop)
        
        return domain

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            if len(self.shape) < 2:
                return self

    def domain_definition(self, allow_empty=None):
        base = self.base
        
        from sympy.logic.boolalg import And
        eqs = []
        for i, sliced in enumerate(self.slices):
            start, stop, step = sliced.slice_args
            size = base.shape[i]
            eqs += [start >= 0, start <= stop if allow_empty else start < stop, stop <= size, step >= 0]
            
        return And(*eqs) 

    def _subs(self, old, new, **kwargs):
        if self == old:
            return new
        if self.base == old:
            return new[self.args[1:]]
        if old.is_Sliced and old.base == self.base:

# base[      self_start : self_stop]       = self
# 
# base[start            :            stop] = old
# 
# new = old
# 
# base[self_start] = base[start:stop][self_start - start] = old[self_start - start] = new[self_start - start]
# base[self_start + 1] = base[start:stop][self_start - start + 1] = old[self_start - start + 1] = new[self_start - start + 1]
# base[self_stop - 1] = base[start:stop][self_stop - 1 - start] = old[self_stop - 1 - start] = new[self_stop - 1 - start]
# 
# new[self_start - start: self_stop - start]
            
            self_start, self_stop = self.index
            start, stop = old.index
            
            if start <= self_start and stop >= self_stop:
                assert new.shape
                return new[self_start - start: self_stop - start]
        return Expr._subs(self, old, new, **kwargs)

    @staticmethod
    def simplify_Lamda(self, squeeze=False):
        expr = self.expr
        slices, indices = expr.slices_indices()
        if len(indices) == 1:
            [var] = indices
            _var, *ab = self.limits[0]
            if var == _var:
                base = expr.base
                if not ab or ab == [0, base.shape[-1]]:
                    if slices[-1].is_Tuple:
                        start, stop, *_ = slices[-1]
                        if start == 0 and stop == base.shape[-2]:
                            expr = base[slices[:-1]].T
                            if limits := self.limits[1:]:
                                expr = self.func(expr, *limits)
                            return expr
                        
                    else:
                        start, stop, step = slices[-1].args
                        if step.is_One and start == 0 and stop == base.shape[-2]:
                            expr = base[slices[:-1]].T
                            if limits := self.limits[1:]:
                                expr = self.func(expr, *limits)
                            return expr
                        
        return self

    @property
    def var(self):
        assert self.base.is_random
        assert not any(index.is_random for index in self.indices)
        return self.base.var[self.indices]

    @property
    def surrogate(self):
        assert self.base.is_random
        assert not any(index.is_random for index in self.indices)
        return self.base.surrogate[self.indices]

    def __and__(self, other):
        """Overloading for & operator"""
        if self.is_random and other.is_random:
            if not other.is_bool:
                other = other.as_boolean()
            return self.as_boolean() & other

        return super(SlicedIndexed, self).__and__(other)

    def _eval_Abs(self):
        if self.is_extended_nonnegative:
            return self
        from sympy import Abs
        return Abs(self, evaluate=False)

# Warning: the following class is obsolete!!! using Symbol.x(shape=(m,n,k)) instead
class IndexedBase(Expr, NotIterable):
    """Represent the base or stem of an indexed object

    The IndexedBase class represent an array that contains elements. The main purpose
    of this class is to allow the convenient creation of objects of the Indexed
    class.  The __getitem__ method of IndexedBase returns an instance of
    Indexed.  Alone, without indices, the IndexedBase class can be used as a
    notation for e.g. matrix equations, resembling what you could do with the
    Symbol class.  But, the IndexedBase class adds functionality that is not
    available for Symbol instances:

      -  An IndexedBase object can optionally store shape information.  This can
         be used in to check array conformance and conditions for numpy
         broadcasting.  (TODO)
      -  An IndexedBase object implements syntactic sugar that allows easy symbolic
         representation of array operations, using implicit summation of
         repeated indices.
      -  The IndexedBase object symbolizes a mathematical structure equivalent
         to arrays, and is recognized as such for code generation and automatic
         compilation and wrapping.

    >>> from sympy.tensor import IndexedBase, Idx
    >>> from sympy import symbols
    >>> A = IndexedBase('A'); A
    A
    >>> type(A)
    <class 'sympy.tensor.indexed.IndexedBase'>

    When an IndexedBase object receives indices, it returns an array with named
    axes, represented by an Indexed object:

    >>> i, j = symbols('i j', integer=True)
    >>> A[i, j, 2]
    A[i, j, 2]
    >>> type(A[i, j, 2])
    <class 'sympy.tensor.indexed.Indexed'>

    The IndexedBase constructor takes an optional shape argument.  If given,
    it overrides any shape information in the indices. (But not the index
    ranges!)

    >>> m, n, o, p = symbols('m n o p', integer=True)
    >>> i = Idx('i', m)
    >>> j = Idx('j', n)
    >>> A[i, j].shape
    (m, n)
    >>> B = IndexedBase('B', shape=(o, p))
    >>> B[i, j].shape
    (o, p)

    Assumptions can be specified with keyword arguments the same way as for Symbol:

    >>> A_real = IndexedBase('A', real=True)
    >>> A_real.is_real
    True
    >>> A != A_real
    True

    Assumptions can also be inherited if a Symbol is used to initialize the IndexedBase:

    >>> I = symbols('I', integer=True)
    >>> C_inherit = IndexedBase(I)
    >>> C_explicit = IndexedBase('I', integer=True)
    >>> C_inherit == C_explicit
    True
    """
    is_commutative = True
    is_symbol = True
    is_Atom = True

    @staticmethod
    def _set_assumptions(obj, assumptions):
        """Set assumptions on obj, making sure to apply consistent values."""
        tmp_asm_copy = assumptions.copy()
        is_commutative = fuzzy_bool(assumptions.get('commutative', True))
        assumptions['commutative'] = is_commutative
        obj._assumptions = StdFactKB(assumptions)
        obj._assumptions._generator = tmp_asm_copy  # Issue #8873

    def __new__(cls, label, shape=None, *, offset=S.Zero, strides=None, **kw_args):
        from sympy import MatrixBase, NDimArray

        assumptions, kw_args = _filter_assumptions(kw_args)
        if isinstance(label, str):
            label = Symbol(label, **assumptions)
        elif isinstance(label, Symbol):
            assumptions = label._merge(assumptions)
        elif isinstance(label, (MatrixBase, NDimArray)):
            return label
        elif isinstance(label, Iterable):
            return _sympify(label)
        else:
            label = _sympify(label)

        if is_sequence(shape):
            shape = Tuple(*shape)
        elif shape is not None:
            shape = Tuple(shape)

        if shape is not None:
            obj = Expr.__new__(cls, label, shape)
        else:
            obj = Expr.__new__(cls, label)
        obj._shape = shape
        obj._offset = offset
        obj._strides = strides
        obj._name = str(label)

        IndexedBase._set_assumptions(obj, assumptions)
        return obj

    @property
    def name(self):
        return self._name

    def _hashable_content(self):
        return super(IndexedBase, self)._hashable_content() + tuple(sorted(self.assumptions0.items()))

    @property
    def assumptions0(self):
        return {k: v for k, v in self._assumptions.items() if v is not None}

    def __getitem__(self, indices, **kw_args):
        if is_sequence(indices):
            # Special case needed because M[*my_tuple] is a syntax error.
            if self.shape and len(self.shape) != len(indices):
                raise IndexException("Rank mismatch.")
            return Indexed(self, *indices, **kw_args)
        else:
            if self.shape and len(self.shape) != 1:
                raise IndexException("Rank mismatch.")
            return Indexed(self, indices, **kw_args)

    def _eval_shape(self):
        """Returns the shape of the ``IndexedBase`` object.

        Examples
        ========

        >>> from sympy import IndexedBase, Idx
        >>> from sympy.abc import x, y
        >>> IndexedBase('A', shape=(x, y)).shape
        (x, y)

        Note: If the shape of the ``IndexedBase`` is specified, it will override
        any shape information given by the indices.

        >>> A = IndexedBase('A', shape=(x, y))
        >>> B = IndexedBase('B')
        >>> i = Idx('i', 2)
        >>> j = Idx('j', 1)
        >>> A[i, j].shape
        (x, y)
        >>> B[i, j].shape
        (2, 1)

        """
        return self._shape

    @property
    def strides(self):
        """Returns the strided scheme for the ``IndexedBase`` object.

        Normally this is a tuple denoting the number of
        steps to take in the respective dimension when traversing
        an array. For code generation purposes strides='C' and
        strides='F' can also be used.

        strides='C' would mean that code printer would unroll
        in row-major order and 'F' means unroll in column major
        order.

        """

        return self._strides

    @property
    def offset(self):
        """Returns the offset for the ``IndexedBase`` object.

        This is the value added to the resulting index when the
        2D Indexed object is unrolled to a 1D form. Used in code
        generation.

        Examples
        ==========
        >>> from sympy.printing import ccode
        >>> from sympy.tensor import IndexedBase, Idx
        >>> from sympy import symbols
        >>> l, m, n, o = symbols('l m n o', integer=True)
        >>> A = IndexedBase('A', strides=(l, m, n), offset=o)
        >>> i, j, k = map(Idx, 'ijk')
        >>> ccode(A[i, j, k])
        'A[l*i + m*j + n*k + o]'

        """
        return self._offset

    @property
    def label(self):
        """Returns the label of the ``IndexedBase`` object.

        Examples
        ========

        >>> from sympy import IndexedBase
        >>> from sympy.abc import x, y
        >>> IndexedBase('A', shape=(x, y)).label
        A

        """
        return self.args[0]

    def _sympystr(self, p):
        return p._print(self.label)


class Idx(Expr):
    """Represents an integer index as an ``Integer`` or integer expression.

    There are a number of ways to create an ``Idx`` object.  The constructor
    takes two arguments:

    ``label``
        An integer or a symbol that labels the index.
    ``range``
        Optionally you can specify a range as either

        * ``Symbol`` or integer: This is interpreted as a dimension. Lower and
          upper bounds are set to ``0`` and ``range - 1``, respectively.
        * ``tuple``: The two elements are interpreted as the lower and upper
          bounds of the range, respectively.

    Note: bounds of the range are assumed to be either integer or infinite (oo
    and -oo are allowed to specify an unbounded range). If ``n`` is given as a
    bound, then ``n.is_integer`` must not return false.

    For convenience, if the label is given as a string it is automatically
    converted to an integer symbol.  (Note: this conversion is not done for
    range or dimension arguments.)

    Examples
    ========

    >>> from sympy import IndexedBase, Idx, symbols, oo
    >>> n, i, L, U = symbols('n i L U', integer=True)

    If a string is given for the label an integer ``Symbol`` is created and the
    bounds are both ``None``:

    >>> idx = Idx('qwerty'); idx
    qwerty
    >>> idx.lower, idx.upper
    (None, None)

    Both upper and lower bounds can be specified:

    >>> idx = Idx(i, (L, U)); idx
    i
    >>> idx.lower, idx.upper
    (L, U)

    When only a single bound is given it is interpreted as the dimension
    and the lower bound defaults to 0:

    >>> idx = Idx(i, n); idx.lower, idx.upper
    (0, n - 1)
    >>> idx = Idx(i, 4); idx.lower, idx.upper
    (0, 3)
    >>> idx = Idx(i, oo); idx.lower, idx.upper
    (0, oo)

    """

    is_integer = True
    is_finite = True
    is_real = True
    is_symbol = True
    is_Atom = True
    _diff_wrt = True

    @cacheit
    def __new__(cls, label, range=None, **kw_args):
        if isinstance(label, str):
            label = Symbol(label, integer=True)
        label, range = list(map(sympify, (label, range)))

        if label.is_Number:
            if not label.is_integer:
                raise TypeError("Index is not an integer number.")
            return label

        if not label.is_integer:
            raise TypeError("Idx object requires an integer label.")

        elif is_sequence(range):
            if len(range) != 2:
                raise ValueError("""
                    Idx range tuple must have length 2, but got %s""" % len(range))
            for bound in range:
                if (bound.is_integer == False and bound is not S.Infinity
                        and bound is not S.NegativeInfinity):
                    raise TypeError("Idx object requires integer bounds.")
            args = label, Tuple(*range)
        elif isinstance(range, Expr):
            if not (range.is_integer or range is S.Infinity):
                raise TypeError("Idx object requires an integer dimension.")
            args = label, Tuple(0, range - 1)
        elif range:
            raise TypeError("""
                The range must be an ordered iterable or
                integer SymPy expression.""")
        else:
            args = label,

        obj = Expr.__new__(cls, *args, **kw_args)
        obj._assumptions["finite"] = True
        obj._assumptions["real"] = True
        return obj

    @property
    def label(self):
        """Returns the label (Integer or integer expression) of the Idx object.

        Examples
        ========

        >>> from sympy import Idx, Symbol
        >>> x = Symbol('x', integer=True)
        >>> Idx(x).label
        x
        >>> j = Symbol('j', integer=True)
        >>> Idx(j).label
        j
        >>> Idx(j + 1).label
        j + 1

        """
        return self.args[0]

    @property
    def lower(self):
        """Returns the lower bound of the ``Idx``.

        Examples
        ========

        >>> from sympy import Idx
        >>> Idx('j', 2).lower
        0
        >>> Idx('j', 5).lower
        0
        >>> Idx('j').lower is None
        True

        """
        try:
            return self.args[1][0]
        except IndexError:
            return

    @property
    def upper(self):
        """Returns the upper bound of the ``Idx``.

        Examples
        ========

        >>> from sympy import Idx
        >>> Idx('j', 2).upper
        1
        >>> Idx('j', 5).upper
        4
        >>> Idx('j').upper is None
        True

        """
        try:
            return self.args[1][1]
        except IndexError:
            return

    def _sympystr(self, p):
        return p._print(self.label)

    @property
    def name(self):
        return self.label.name if self.label.is_Symbol else str(self.label)

    def _eval_free_symbols(self):
        return {self}

    def __le__(self, other):
        if isinstance(other, Idx):
            other_upper = other if other.upper is None else other.upper
            other_lower = other if other.lower is None else other.lower
        else:
            other_upper = other
            other_lower = other

        if self.upper is not None and (self.upper <= other_lower) == True:
            return True
        if self.lower is not None and (self.lower > other_upper) == True:
            return False
        return super(Idx, self).__le__(other)

    def __ge__(self, other):
        if isinstance(other, Idx):
            other_upper = other if other.upper is None else other.upper
            other_lower = other if other.lower is None else other.lower
        else:
            other_upper = other
            other_lower = other

        if self.lower is not None and (self.lower >= other_upper) == True:
            return True
        if self.upper is not None and (self.upper < other_lower) == True:
            return False
        return super(Idx, self).__ge__(other)

    def __lt__(self, other):
        if isinstance(other, Idx):
            other_upper = other if other.upper is None else other.upper
            other_lower = other if other.lower is None else other.lower
        else:
            other_upper = other
            other_lower = other

        if self.upper is not None and (self.upper < other_lower) == True:
            return True
        if self.lower is not None and (self.lower >= other_upper) == True:
            return False
        return super(Idx, self).__lt__(other)

    def __gt__(self, other):
        if isinstance(other, Idx):
            other_upper = other if other.upper is None else other.upper
            other_lower = other if other.lower is None else other.lower
        else:
            other_upper = other
            other_lower = other

        if self.lower is not None and (self.lower > other_upper) == True:
            return True
        if self.upper is not None and (self.upper <= other_lower) == True:
            return False
        return super(Idx, self).__gt__(other)


def slices_contains_slices(slices, _slices):
    return all(_start >= start and _stop <= stop for (start, stop), (_start, _stop) in zip(slices, _slices))

def slices_contains_indices(slices, indices):
    from sympy import Range
    return all(Range(a, b).conditionally_contains(i) for (a, b), i in zip(slices, indices))

def indices_contains_indices(indices, _indices):
    if len(_indices) < len(indices):
        return False

    if len(_indices) > len(indices):
        return _indices[:len(indices)] == indices
    
    return _indices == indices


#given: lhs, rhs are sets of symbols
def index_intersect(lhs, rhs):
    vars = set()
    for v in lhs:
        for _v in rhs:
            if (_v := _v.index_intersect(v)) is not None:
                vars.add(_v)

    return vars

#given: lhs, rhs are each a set of symbols, or a symbol
def index_complement(lhs, rhs):
    if isinstance(lhs, set):
        ret = set()
        for v in lhs:
            ret |= index_complement(v, rhs)
    
        return ret
    
    if isinstance(rhs, set):
        if not rhs:
            return {lhs}
        
        for v in rhs:
            lhs = index_complement(lhs, v)
        
        return lhs

    if ret := lhs.index_complement(rhs):
        if isinstance(ret, set):
            return ret
        return {ret}

    return set()

def expand_indices(limit, indices):
    i, a, b = limit
    for t, d in enumerate(indices):
        if d.is_Tuple:
            start = None
            if d[0]._has(i):
                h, k = d[0].of_simple_poly(i)
                if k:
                    if k < 0:
                        k = -k
                        a, b = b - 1, a - 1
    
                    if k > 0:
                        if k > 1:
                            print('unresolved cases')
                        start = (a * k + h, b * k + h)
            else:
                start = d[0]
    
            if start is None:
                continue
    
            stop = None
            if d[1]._has(i):
                h, k = d[1].of_simple_poly(i)
                if k:
                    if k < 0:
                        k = -k
                        a, b = b - 1, a - 1
    
                    if k > 0:
                        if k > 1:
                            print('unresolved cases')
                        stop = (a * k + h, b * k + h)
            else:
                stop = d[1]
    
            if stop is None:
                continue
    
            if isinstance(start, tuple):
                if isinstance(stop, tuple):
                    args = (start[0], stop[1]) 
                else:
                    args = (start[0], stop)
            else:
                if isinstance(stop, tuple):
                    args = (start, stop[1]) 
                else:
                    continue
    
            return t, slice(*args)
            
        else:
            h, k = d.of_simple_poly(i)
            if k:
                if k < 0:
                    k = -k
                    a, b = b - 1, a - 1
    
                if k > 0:
                    if k > 1:
                        print('unresolved cases')
                    return t, Tuple(a * k + h, b * k + h)