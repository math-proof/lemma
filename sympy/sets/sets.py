from itertools import product
import inspect

from sympy.core.basic import Basic
from sympy.core.compatibility import (iterable, ordered, PY3)
from sympy.core.cache import cacheit
from sympy.core.evalf import EvalfMixin
from sympy.core.parameters import global_parameters
from sympy.core.expr import Expr
from sympy.core.logic import fuzzy_bool, fuzzy_and, fuzzy_et, fuzzy_ou
from sympy.core.mul import Mul
from sympy.core.operations import LatticeOp
from sympy.core.relational import Eq, Ne, Equal
from sympy.core.singleton import S
from sympy.core.symbol import Symbol, Dummy, _uniquely_named_symbol, dtype
from sympy.core.sympify import _sympify, sympify
from sympy.logic.boolalg import And, Or
from sympy.sets.contains import Element
from sympy.utilities.iterables import sift
from sympy.utilities.misc import func_name, filldedent

from mpmath import mpi, mpf


def is_set(s):
    if isinstance(s, set):
        return True
    if isinstance(s, Basic): 
        return s.is_set


class Set(Basic):
    """
    The base class for any kind of set.

    This is not meant to be used directly as a container of items. It does not
    behave like the builtin ``set``; see :class:`FiniteSet` for that.

    Real intervals are represented by the :class:`Interval` class and unions of
    sets by the :class:`Union` class. The empty set is represented by the
    :class:`EmptySet` class and available as a singleton as ``EmptySet()``.
    """
    is_number = False
    is_set = True
    is_iterable = False
    is_interval = False

    def _eval_is_finiteset(self):
        ...
        
    @property
    def domain(self):
        return self.universalSet
    
    def _eval_shape(self):
        return ()

    def image_set(self):
        ...

    def element_symbol(self, excludes=None):
        return self.generate_var(excludes, **self.etype.dict)

    @property
    def dtype(self):
        assert self.etype is not None, self
        return self.etype.set

    def could_extract_minus_sign(self):
        return False

    @staticmethod
    def _infimum_key(expr):
        """
        Return infimum (if possible) else S.Infinity.
        """
        try:
            infimum = expr.inf
            assert infimum.is_comparable
        except (NotImplementedError,
                AttributeError, AssertionError, ValueError):
            infimum = S.Infinity
        return infimum

    def union(self, other):
        """
        Returns the union of 'self' and 'other'.

        Examples
        ========

        As a shortcut it is possible to use the '+' operator:

        >>> from sympy import Interval, FiniteSet
        >>> Interval(0, 1).union(Interval(2, 3))
        Union(Interval(0, 1), Interval(2, 3))
        >>> Interval(0, 1) + Interval(2, 3)
        Union(Interval(0, 1), Interval(2, 3))

        Similarly it is possible to use the '-' operator for set differences:

        >>> Interval(0, 2) - Interval(0, 1)
        Interval.Lopen(1, 2)
        >>> Interval(1, 3) - FiniteSet(2)
        Union(Interval.Ropen(1, 2), Interval.Lopen(2, 3))

        """
        return Union(self, other)

    def intersect(self, other):
        """
        Returns the intersection of 'self' and 'other'.

        >>> from sympy import Interval

        >>> Interval(1, 3).intersect(Interval(1, 2))
        Interval(1, 2)

        >>> from sympy import imageset, Lambda, symbols, S
        >>> n, m = symbols('n m')
        >>> a = imageset(Lambda(n, 2*n), S.Integers)
        >>> a.intersect(imageset(Lambda(m, 2*m + 1), S.Integers))
        EmptySet()

        """
        return Intersection(self, other)

    def intersection(self, other):
        """
        Alias for :meth:`intersect()`
        """
        return self.intersect(other)

    def is_disjoint(self, other):
        """
        Returns True if 'self' and 'other' are disjoint

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 2).is_disjoint(Interval(1, 2))
        False
        >>> Interval(0, 2).is_disjoint(Interval(3, 4))
        True

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Disjoint_sets
        """
        return self.intersect(other).is_EmptySet

    def isdisjoint(self, other):
        """
        Alias for :meth:`is_disjoint()`
        """
        return self.is_disjoint(other)

    def complement(self, universe):
        r"""
        The complement of 'self' w.r.t the given universe.

        Examples
        ========

        >>> from sympy import Interval, S
        >>> Interval(0, 1).complement(Reals)
        Union(Interval.open(-oo, 0), Interval.open(1, oo))

        >>> Interval(0, 1).complement(UniversalSet())
        UniversalSet \ Interval(0, 1)

        """
        return Complement(universe, self)

    def _complement(self, other):
        # this behaves as other - self
        if other.is_ProductSet:
            from sympy import FiniteSet
            # For each set consider it or it's complement
            # We need at least one of the sets to be complemented
            # Consider all 2^n combinations.
            # We can conveniently represent these options easily using a
            # ProductSet

            # XXX: this doesn't work if the dimensions of the sets isn't same.
            # A - B is essentially same as A if B has a different
            # dimensionality than A
            switch_sets = ProductSet(FiniteSet(o, o - s) for s, o in zip(self.sets, other.sets))
            product_sets = (ProductSet(*s) for s in switch_sets)
            # Union of all combinations but this one
            return Union(*(p for p in product_sets if p != other))

        elif other.is_Interval:
            if self.is_Interval:
                U = other.etype.universalSet
                return Intersection(other, self.complement(U))

        elif other.is_Range:
            if self.is_Range and self.step.is_One:
                from sympy.sets import Integers
                return Intersection(other, self.complement(Integers))

        elif other.is_Union:
            simplified = []
            unsimplified = []
            hit = False
            for arg in other.args:
                diff = Complement(arg, self)
                if diff.is_Complement and diff.args[1] == self:
                    hit = diff.args[0] != arg
                    unsimplified.append(diff.args[0])
                else: 
                    hit = True
                    simplified.append(diff)
            if hit:
                simplified = Union(*simplified, evaluate=False) if simplified else self.etype.emptySet
                unsimplified = Complement(Union(*unsimplified, evaluate=False), self, evaluate=False) if unsimplified else self.etype.emptySet
                return simplified | unsimplified

        elif other.is_Complement:
            if other.args[0] in self:
                return self.etype.emptySet
            return Complement(other.args[0], Union(other.args[1], self), evaluate=False)

        elif other.is_EmptySet:
            return other

        elif other.is_FiniteSet:
            sifted = sift(other, lambda x: fuzzy_bool(self.contains(x)))
            # ignore those that are contained in self
            return Union(FiniteSet(*(sifted[False])), Complement(FiniteSet(*(sifted[None])), self, evaluate=False) if sifted[None] else self.etype.emptySet)

    def symmetric_difference(self, other):
        """
        Returns symmetric difference of `self` and `other`.

        Examples
        ========

        >>> from sympy import Interval, S
        >>> Interval(1, 3).symmetric_difference(Reals)
        Union(Interval.open(-oo, 1), Interval.open(3, oo))
        >>> Interval(1, 10).symmetric_difference(Reals)
        Union(Interval.open(-oo, 1), Interval.open(10, oo))

        >>> from sympy import S, EmptySet
        >>> Reals.symmetric_difference(EmptySet())
        Reals

        References
        ==========
        .. [1] https://en.wikipedia.org/wiki/Symmetric_difference

        """
        return SymmetricDifference(self, other)

    def _symmetric_difference(self, other):
        return Union(Complement(self, other), Complement(other, self))

    @property
    def inf(self):
        """
        The infimum of 'self'

        Examples
        ========

        >>> from sympy import Interval, Union
        >>> Interval(0, 1).inf
        0
        >>> Union(Interval(0, 1), Interval(2, 3)).inf
        0

        """
        return self._inf

    @property
    def _inf(self):
        raise NotImplementedError("(%s)._inf" % self)

    @property
    def sup(self):
        """
        The supremum of 'self'

        Examples
        ========

        >>> from sympy import Interval, Union
        >>> Interval(0, 1).sup
        1
        >>> Union(Interval(0, 1), Interval(2, 3)).sup
        3

        """
        return self._sup

    @property
    def _sup(self):
        raise NotImplementedError("(%s)._sup" % self)

    def _contains(self, other):
        raise NotImplementedError("(%s)._contains(%s)" % (self, other))

    def is_subset(self, other):
        """
        Returns True if 'self' is a subset of 'other'.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 0.5).is_subset(Interval(0, 1))
        True
        >>> Interval(0, 1).is_subset(Interval(0, 1, left_open=True))
        False

        """
        if other.is_set:
            # XXX issue 16873
            # self might be an unevaluated form of self
            # so the equality test will fail
            return self.intersect(other) == self
        else:
            raise ValueError("Unknown argument '%s'" % other)

    def issubset(self, other):
        """
        Alias for :meth:`is_subset()`
        """
        return self.is_subset(other)

    def is_proper_subset(self, other):
        """
        Returns True if 'self' is a proper subset of 'other'.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 0.5).is_proper_subset(Interval(0, 1))
        True
        >>> Interval(0, 1).is_proper_subset(Interval(0, 1))
        False

        """
        if other.is_set:
            return self != other and self.is_subset(other)
        else:
            raise ValueError("Unknown argument '%s'" % other)

    def is_superset(self, other):
        """
        Returns True if 'self' is a superset of 'other'.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 0.5).is_superset(Interval(0, 1))
        False
        >>> Interval(0, 1).is_superset(Interval(0, 1, left_open=True))
        True

        """
        if other.is_set:
            return other.is_subset(self)
        else:
            raise ValueError("Unknown argument '%s'" % other)

    def issuperset(self, other):
        """
        Alias for :meth:`is_superset()`
        """
        return self.is_superset(other)

    def is_proper_superset(self, other):
        """
        Returns True if 'self' is a proper superset of 'other'.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 1).is_proper_superset(Interval(0, 0.5))
        True
        >>> Interval(0, 1).is_proper_superset(Interval(0, 1))
        False

        """
        if other.is_set:
            return self != other and self.is_superset(other)
        else:
            raise ValueError("Unknown argument '%s'" % other)

    def _eval_powerset(self):
        raise NotImplementedError('Power set not defined for: %s' % self.func)

    def powerset(self):
        """
        Find the Power set of 'self'.

        Examples
        ========

        >>> from sympy import FiniteSet, EmptySet
        >>> A = EmptySet()
        >>> A.powerset()
        {EmptySet()}
        >>> A = FiniteSet(1, 2)
        >>> a, b, c = FiniteSet(1), FiniteSet(2), FiniteSet(1, 2)
        >>> A.powerset() == FiniteSet(a, b, c, EmptySet())
        True

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Power_set

        """
        return self._eval_powerset()

    @property
    def measure(self):
        """
        The (Lebesgue) measure of 'self'

        Examples
        ========

        >>> from sympy import Interval, Union
        >>> Interval(0, 1).measure
        1
        >>> Union(Interval(0, 1), Interval(2, 3)).measure
        2

        """
        return self._measure

    @property
    def boundary(self):
        """
        The boundary or frontier of a set

        A point x is on the boundary of a set S if

        1.  x is in the closure of S.
            I.e. Every neighborhood of x contains a point in S.
        2.  x is not in the interior of S.
            I.e. There does not exist an open set centered on x contained
            entirely within S.

        There are the points on the outer rim of S.  If S is open then these
        points need not actually be contained within S.

        For example, the boundary of an interval is its start and end points.
        This is true regardless of whether or not the interval is open.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 1).boundary
        {0, 1}
        """
        return self._boundary

    @property
    def is_open(self):
        """
        Property method to check whether a set is open.
        A set is open if and only if it has an empty intersection with its
        boundary.

        Examples
        ========
        >>> from sympy import S
        >>> Reals.is_open
        True
        """
        if not Intersection(self, self.boundary):
            return True
        # We can't confidently claim that an intersection exists
        return None

    @property
    def is_closed(self):
        """
        A property method to check whether a set is closed. A set is closed
        if it's complement is an open set.

        Examples
        ========
        >>> from sympy import Interval
        >>> Interval(0, 1).is_closed
        True
        """
        return self.boundary.is_subset(self)

    @property
    def closure(self):
        """
        Property method which returns the closure of a set.
        The closure is defined as the union of the set itself and its
        boundary.

        Examples
        ========
        >>> from sympy import S, Interval
        >>> Reals.closure
        Reals
        >>> Interval(0, 1).closure
        Interval(0, 1)
        """
        return self + self.boundary

    @property
    def interior(self):
        """
        Property method which returns the interior of a set.
        The interior of a set S consists all points of S that do not
        belong to the boundary of S.

        Examples
        ========
        >>> from sympy import Interval
        >>> Interval(0, 1).interior
        Interval.open(0, 1)
        >>> Interval(0, 1).boundary.interior
        EmptySet()
        """
        return self - self.boundary

    @property
    def _boundary(self):
        raise NotImplementedError()

    @property
    def _measure(self):
        raise NotImplementedError("(%s)._measure" % self)

    def __add__(self, other):
        raise Exception("could not add %s, %s" % (self, other))

    def __or__(self, other):
        return self.union(other)

    def __and__(self, other):
        return self.intersect(other)

    def __matmul__(self, other):
        return ProductSet(self, other)

    def __mul__(self, other):
        raise Exception("could not multiply %s, %s" % (self, other))

    def __xor__(self, other):
        return SymmetricDifference(self, other)

    def __pow__(self, exp):
        if not sympify(exp).is_Integer and exp >= 0:
            raise ValueError("%s: Exponent must be a positive Integer" % exp)
        return ProductSet([self] * exp)

    def __sub__(self, other): 
        return Complement(self, other)

    # performing other in self
    def __contains__(self, other):
        contains = self.contains_with_subset(other)
        if contains is not None:
            return contains
        
        return sympify(self.contains(other))

    def conjugate(self):
        from sympy.functions.elementary.complexes import conjugate
        return conjugate(self)

    def _eval_conjugate(self):
        return

    def _eval_is_nonempty(self):
        if self.shape:
            return

        zero = self.is_empty
        if zero:
            return False

        if zero == False:
            return True


class ProductSet(Set):
    """
    Represents a Cartesian Product of Sets.

    Returns a Cartesian product given several sets as either an iterable
    or individual arguments.

    Can use '*' operator on any sets for convenient shorthand.

    Examples
    ========

    >>> from sympy import Interval, FiniteSet, ProductSet
    >>> I = Interval(0, 5); S = FiniteSet(1, 2, 3)
    >>> ProductSet(I, S)
    Interval(0, 5) x {1, 2, 3}

    >>> (2, 2) in ProductSet(I, S)
    True

    >>> Interval(0, 1) * Interval(0, 1) # The unit square
    Interval(0, 1) x Interval(0, 1)

    >>> coin = FiniteSet('H', 'T')
    >>> set(coin**2)
    {(H, H), (H, T), (T, H), (T, T)}


    Notes
    =====

    - Passes most operations down to the argument sets
    - Flattens Products of ProductSets

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Cartesian_product
    """
    def intersection_sets(self, b):
        if not b.is_ProductSet:
            return None

        if len(b.args) != len(self.args):
            return EmptySet()
        return ProductSet(i.intersect(j)
                for i, j in zip(self.sets, b.sets))

    def union_sets(self, b):
        if b.is_ProductSet:
            if b.is_subset(self):
                return self
            if len(b.args) != len(self.args):
                return None
            if self.args[0] == b.args[0]:
                return self.args[0] * Union(ProductSet(self.args[1:]),
                                            ProductSet(b.args[1:]))
            if self.args[-1] == b.args[-1]:
                return Union(ProductSet(self.args[:-1]),
                             ProductSet(b.args[:-1])) * self.args[-1]
            return None
        if b.is_subset(self):
            return self
        return None

    def __new__(cls, *sets, **assumptions):

        def flatten(arg):
            if isinstance(arg, Set):
                if arg.is_ProductSet:
                    return sum(map(flatten, arg.args), [])
                else:
                    return [arg]
            elif iterable(arg):
                return sum(map(flatten, arg), [])

            if arg.is_set:
                return [arg]

            raise TypeError("Input must be Sets or iterables of Sets")

        sets = flatten(list(sets))

        if EmptySet() in sets or len(sets) == 0:
            return EmptySet()

        if len(sets) == 1:
            return sets[0]

        return Basic.__new__(cls, *sets, **assumptions)

    def _eval_Eq(self, other):
        if not other.is_ProductSet:
            return

        if len(self.args) != len(other.args):
            return S.false

        return And(*(Eq(x, y) for x, y in zip(self.args, other.args)))

    def _contains(self, element):
        """
        'in' operator for ProductSets

        Examples
        ========

        >>> from sympy import Interval
        >>> (2, 3) in Interval(0, 5) * Interval(0, 5)
        True

        >>> (10, 10) in Interval(0, 5) * Interval(0, 5)
        False

        Passes operation on to constituent sets
        """
        try:
            if len(element) != len(self.args):
                return S.false
        except TypeError:  # maybe element isn't an iterable
            return S.false
        return And(*[s.contains(item) for s, item in zip(self.sets, element)])

    @property
    def sets(self):
        return self.args

    @property
    def _boundary(self):
        return Union(*(ProductSet(b + b.boundary if i != j else b.boundary
                                for j, b in enumerate(self.sets))
                                for i, a in enumerate(self.sets)))

    @property
    def is_iterable(self):
        """
        A property method which tests whether a set is iterable or not.
        Returns True if set is iterable, otherwise returns False.

        Examples
        ========

        >>> from sympy import FiniteSet, Interval, ProductSet
        >>> I = Interval(0, 1)
        >>> A = FiniteSet(1, 2, 3, 4, 5)
        >>> I.is_iterable
        False
        >>> A.is_iterable
        True

        """
        return all(s.is_iterable for s in self.sets)

    def __iter__(self):
        """
        A method which implements is_iterable property method.
        If self.is_iterable returns True (both constituent sets are iterable),
        then return the Cartesian Product. Otherwise, raise TypeError.
        """
        if self.is_iterable:
            return product(*self.sets)
        else:
            raise TypeError("Not all constituent sets are iterable")

    @property
    def _measure(self):
        measure = 1
        for s in self.sets:
            measure *= s.measure
        return measure

    def __len__(self):
        return Mul(*[len(s) for s in self.args])

    def __bool__(self):
        return all([bool(s) for s in self.args])

    def __neg__(self):
        return self.func(*(-arg for arg in self.args))

    def _sympystr(self, p):
        return ' @ '.join(p._print(s) for s in self.sets)

    def _lean(self, p):
        return ' @ '.join(p._print(s) for s in self.sets)
    

class CartesianSpace(Set):

    def __new__(cls, domain, *dimension):
        if not dimension:
            return domain
        if len(dimension) == 1:
            d = dimension[0]
            assert d, "dimension must be nonzero"
            if dimension[0] == 1:
                return domain
            if isinstance(d, int):
                dimension = (sympify(d),)
        return Set.__new__(cls, domain, *dimension)

    @cacheit
    def _eval_domain_defined(self, x, **_): 
        return self.space.domain_defined(x) & Intersection(*(x.domain_conditioned(d > 0) for d in self.space_shape))

    @property
    def domain(self):
        return self.universalSet
    
    @property
    def space(self):
        return self.args[0]

    def _eval_shape(self):
        return ()
    
    @property
    def etype(self):
        return self.space.etype[self.space_shape]

    @property
    def space_shape(self):
        return self.args[1:]

    def _eval_is_extended_integer(self):
        return self.space.is_extended_integer

    def _contains(self, other):
        from sympy import Range
        if tuple(self.etype.shape) != tuple(other.shape):
            print("self.etype.shape = %s, other.shape = %s" % (self.etype.shape, other.shape), "\nthese shape might contain unsimplified expression")
            return
        
        if self.is_UniversalSet:
            if other.dtype in self.etype.dtype:
                return S.true

        if other.is_Sliced or other.is_Symbol:
            n = other.shape[0]
            i = Dummy('i', domain=Range(n))
            space_shape = self.space_shape[1:]
            if space_shape:
                domain = self.func(self.space, *space_shape)
            else:
                domain = self.space
                
            cond = Element(other[i], domain)
            if cond:
                return cond
            if cond == False:
                return cond
        elif other.is_BlockMatrix:
            if other.axis == 0:
                space_shape = self.space_shape[1:]
                if space_shape:
                    domain = self.func(self.space, *space_shape)
                else:
                    domain = self.space
                
                for block in other.args:
                    if block.shape: 
                        n = block.shape[0]
                        i = Dummy('i', domain=Range(n))
                        cond = Element(other[i], domain)
                    else:
                        cond = Element(block, domain)
                        
                    if cond:
                        continue
                    if cond == False:
                        return cond
                    return
                return S.true
        elif other.is_DenseMatrix:
            contains = None
            for arg in other.args:
                cond = Element(arg, self.space)
                if cond:
                    if contains is None:
                        contains = S.true
                    elif contains == False:
                        return
                elif cond == False:
                    if contains is None:
                        contains = S.false
                    elif contains:
                        return
            return contains

    def __mul__(self, other):
        if other.is_set:
            assert len(other.etype.shape) < len(self.etype.shape)
        return self
    
    def __add__(self, other):
        if other.is_CartesianSpace:
            if len(self.space_shape) > len(other.space_shape):
                assert self.space_shape[:len(other.space_shape)] == other.space_shape
                shape = self.space_shape
            elif len(self.space_shape) < len(other.space_shape):
                assert self.space_shape == other.space_shape[len(self.space_shape):]
                shape = other.space_shape
            else:
                if self.space_shape != other.space_shape:
                    print('shape might contain unsimplified expression:\n', self.space_shape, other.space_shape)
                shape = self.space_shape
            return self.func(self.space + other.space, *shape)
        if other.is_set:
            assert len(other.etype.shape) < len(self.etype.shape)
        return self
    
    def intersection_sets(self, b):
        if b.is_CartesianSpace:
            assert self.space_shape == b.space_shape
            return self.func(self.space & b.space, *self.space_shape)
        elif b.is_symbol:
            etype = b.etype
            if etype.as_Set() in self:
                return b

    def _latex(self, p):
        space_shape = self.space_shape
        space_shape = r' \times '.join(p._print(s) for s in space_shape)
        return "{%s}^{%s}" % (p._print(self.space), space_shape)

    @classmethod
    def simplify_Element(cls, self, e, s):
        k = self.generate_var(integer=True)
        n = e.shape[0]
        if n.is_Infinity:
            return self.func(e[k], cls(s.space, *s.space_shape[1:]))
    
    @classmethod
    def simplify_NotElement(cls, self, e, s): 
        k = self.generate_var(integer=True)
        n = e.shape[0]
        if n.is_Infinity:
            return self.func(e[k], cls(s.space, *s.space_shape[1:]))
    
    def _eval_Subset_reversed(self, lhs): 
        if lhs.is_Symbol:
            if lhs.etype.as_Set() in self:
                return S.true

    @property
    def is_UniversalSet(self):
        return self.space.is_UniversalSet

    def _eval_is_empty(self):
        return self.space.is_empty

    def _eval_is_finiteset(self):
        space, *space_shape = self.args
        is_finiteset = self.space.is_finiteset
        if is_finiteset:
            for d in space_shape:
                is_infinite = d.is_infinite
                if is_infinite:
                    return False
                
                if is_infinite is None:
                    return
            return True

        return is_finiteset


class Interval(Set, EvalfMixin):
    """
    Represents a real interval as a Set.

    Usage:
        Returns an interval with end points "start" and "end".

        For left_open=True (default left_open is False) the interval
        will be open on the left. Similarly, for right_open=True the interval
        will be open on the right.

    Examples
    ========

    >>> from sympy import Symbol, Interval
    >>> Interval(0, 1)
    Interval(0, 1)
    >>> Interval.Ropen(0, 1)
    Interval.Ropen(0, 1)
    >>> Interval.Ropen(0, 1)
    Interval.Ropen(0, 1)
    >>> Interval.Lopen(0, 1)
    Interval.Lopen(0, 1)
    >>> Interval.open(0, 1)
    Interval.open(0, 1)

    >>> a = Symbol('a', real=True)
    >>> Interval(0, a)
    Interval(0, a)

    Notes
    =====
    - Only real end points are supported
    - Interval(a, b) with a > b will return the empty set
    - Use the evalf() method to turn an Interval into an mpmath
      'mpi' interval instance

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Interval_%28mathematics%29
    """

    def structurally_equal(self, other):
        if not isinstance(other, self.func) or len(self.args) != len(other.args):
            return False
        if self.left_open != other.left_open or self.right_open != other.right_open:
            return False
        for x, y in zip(self.args[:3], other.args[:3]):
            if not x.structurally_equal(y):
                return False
        return True

    def simplify(self, deep=False, **kwargs):
        if deep:
            hit = False
            args = [*self.args]
            for i, arg in enumerate(self.args[:3]): 
                _arg = arg.simplify(deep=deep)                

                if _arg != arg:
                    hit = True
                args[i] = _arg
            if hit:
                return self.func(*args).simplify()
        
        return self

    @property
    def is_UniversalSet(self):
        return self.start.is_NegativeInfinity and self.stop.is_Infinity and \
            (self.left_open and self.right_open or not self.left_open and not self.right_open)
    
    def intersection_sets(self, b):
        if not (b.is_Interval or b.is_Range):
            if self.is_UniversalSet:
                if b.etype in self.etype:
                    return b
            return
        # handle cases like (-oo, oo) and [-oo, oo]
        if self.start.is_NegativeInfinity and self.stop.is_Infinity:
            if b.etype.is_real:
                return b
            
            if b.etype.is_extended_real:
                from sympy import NotElement
                if self.left_open:
                    if self.right_open:
                        # self = (-oo, oo)
                        ...
                    else:
                        # self = (-oo, oo]
                        if S.Infinity in b and NotElement(S.NegativeInfinity, b):
                            return b
                else:
                    if self.right_open:
                        # self = [-oo, oo)
                        if S.NegativeInfinity in b and NotElement(S.Infinity, b):
                            return b
                    else:
                        # self = [-oo, oo]
                        if S.Infinity in b and S.NegativeInfinity in b:
                            return b

        # We can't intersect [0,3] with [x,6] -- we don't know if x>0 or x<0
        if not self._is_comparable(b): 
 
            if b.etype.is_integer:
                return self.copy(integer=True) & b
            
            from sympy import Min, Max
            if self.left_open:
                if b.left_open:
                    start = Max(self.start, b.start) 
                    left_open = True
                else:
                    if self.start < b.start:
                        start = b.start
                        left_open = False
                    elif self.start >= b.start:
#                             (a, b), [a', b']
                        start = self.start
                        left_open = True
                    else:
                        return
                        
                if self.right_open: 
                    if b.right_open: 
                        stop = Min(self.stop, b.stop)
                        right_open = True
                    else:
                        if b.stop < self.stop:
                            stop = b.stop
                            right_open = False
                        elif b.stop >= self.stop:
                            stop = self.stop
                            right_open = True
                        else:
                            return
                else:
                    if b.right_open:
                        if self.stop >= b.stop:
                            stop = b.stop
                            right_open = True
                        elif self.stop < b.stop:
                            stop = self.stop
                            right_open = False
                        else:
                            return
                    else:
                        stop = Min(self.stop, b.stop)
                        right_open = False
            else:
                if b.left_open:
                    if self.start <= b.start:
                        start = b.start
                        left_open = True
                    elif self.start > b.start:
                        start = self.start
                        left_open = False
                    else:
                        return
                else:
                    start = Max(self.start, b.start)
                    left_open = False
                    
                if self.right_open: 
                    if b.right_open: 
                        stop = Min(self.stop, b.stop)
                        right_open = True
                    else:
                        if self.stop > b.stop:
                            stop = b.stop
                            right_open = False
                        elif self.stop <= b.stop:
#                                 [a, b), [a, b']
                            stop = self.stop
                            right_open = True
                        else: 
                            return
                else:
                    if b.right_open:
                        if self.stop < b.stop:
                            stop = self.stop
                            right_open = False
                        elif self.stop >= b.stop:
                            stop = b.stop
                            right_open = True
                        else:
                            return
                    else:
                        stop = Min(self.stop, b.stop)
                        right_open = False
                        
            return Interval(start, stop, left_open=left_open, right_open=right_open)                            

        empty = False

        if self.start <= b.stop and b.start <= self.stop:
            # Get topology right.
            if self.start < b.start:
                start = b.start
                left_open = b.left_open
            elif self.start > b.start:
                start = self.start
                left_open = self.left_open
            else:
                start = self.start
                left_open = self.left_open or b.left_open

            if self.stop < b.stop:
                stop = self.stop
                right_open = self.right_open
            elif self.stop > b.stop:
                stop = b.stop
                right_open = b.right_open
            else:
                stop = self.stop
                right_open = self.right_open or b.right_open

            if stop - start == 0 and (left_open or right_open):
                empty = True
        else:
            empty = True

        if empty:
            return self.etype.emptySet

        interval = self.func(start, stop, left_open=left_open, right_open=right_open)
        if b.etype.is_integer:
            return interval.copy(integer=True)
        return interval

    def _union_sets(self, b): 
        if self.max() in b:
            from sympy import Min
            return b.copy(start=Min(self.min(), b.min()), left_open=False, integer=None)
        
        if self.min() in b:
            from sympy import Max
            return b.copy(stop=Max(self.max(), b.max()), right_open=False, integer=None)
        
        if self in b:
            return b
        
        if b in self:
            return self
        
        if self.right_open and not b.left_open:
            if self.stop == b.start and b.start <= b.stop:
                if self.left_open:
                    if self.stop > self.start:
                        return Interval(self.start, b.stop, left_open=True, right_open=b.right_open)
                else:
                    if self.stop >= self.start:
                        return Interval(self.start, b.stop, left_open=False, right_open=b.right_open)
        elif not self.right_open and b.left_open:
            if self.stop == b.start and self.start <= self.stop:
                if b.right_open:
                    if b.stop > b.start:
                        return Interval(self.start, b.stop, left_open=self.left_open, right_open=True)
                else:
                    if b.stop >= b.start:
                        return Interval(self.start, b.stop, left_open=self.left_open, right_open=False)
        elif not b.right_open and self.left_open:
            if b.stop == self.start and b.start <= b.stop:
                if self.right_open:
                    if self.stop > self.start:
                        return Interval(b.start, self.stop, left_open=b.left_open, right_open=True)
                else: 
                    if self.stop >= self.start:
                        return Interval(b.start, self.stop, left_open=b.left_open, right_open=False)
        elif b.right_open and not self.left_open:
            if b.stop == self.start and self.start <= self.stop:
                if b.left_open:
                    if b.stop > b.start:
                        return Interval(b.start, self.stop, left_open=True, right_open=self.right_open)
                else:
                    if b.stop >= b.start:
                        return Interval(b.start, self.stop, left_open=False, right_open=self.right_open)
                                     
    def union_sets(self, b):
        if b.is_Interval or b.is_Range:
            if self._is_comparable(b):
                from sympy.functions.elementary.miscellaneous import Min, Max
                # Non-overlapping intervals
                stop = Min(self.stop, b.stop)
                start = Max(self.start, b.start)
                if (stop < start or
                   (stop == start and (stop not in self and stop not in b))):
                    return None
                else:
                    start = Min(self.start, b.start)
                    stop = Max(self.stop, b.stop)

                    left_open = ((self.start != start or self.left_open) and
                                 (b.start != start or b.left_open))
                    right_open = ((self.stop != stop or self.right_open) and
                                  (b.stop != stop or b.right_open))
                    return self.func(start, stop, left_open=left_open, right_open=right_open)
            elif not b.etype.is_integer:
                return self._union_sets(b)
        if b.is_UniversalSet:
            return b
        if b.is_Complement:
            U, A = b.args
            if (U.is_Interval or U.is_Range) and not A & self:
                combined = self | U
                if combined.is_Interval or combined.is_Range:
                    return combined // A

        # If I have open end points and these endpoints are contained in b
        # But only in case, when endpoints are finite. Because
        # interval does not contain oo or -oo.
        open_left_in_b_and_finite = (self.left_open and
                                         sympify(b.contains(self.start)) is S.true and
                                         self.start.is_finite)
        open_right_in_b_and_finite = (self.right_open and
                                          sympify(b.contains(self.stop)) is S.true and
                                          self.stop.is_finite)
        if open_left_in_b_and_finite or open_right_in_b_and_finite:
            # Fill in my end points and return
            left_open = self.left_open and self.start not in b
            right_open = self.right_open and self.stop not in b
            new_a = self.copy(left_open=left_open, right_open=right_open)
            return set((new_a, b))

        if self.etype.is_integer:
            drapeau = False
            stop = self.stop
            right_open = self.right_open
            if right_open:
                if stop in b:
                    drapeau = True
                    right_open = False
            else: 
                if stop + 1 in b:
                    drapeau = True
                    stop += 1

            start = self.start
            left_open = self.left_open
            if left_open:
                if start in b:
                    drapeau = True
                    left_open = False
            else: 
                if start - 1 in b:
                    drapeau = True
                    start -= 1

            if drapeau:
                new_a = self.func(start, stop, left_open=left_open, right_open=right_open, integer=True)
                return set((new_a, b))
        if self.is_UniversalSet:
            return self

    def __new__(cls, start=None, stop=None, **kwargs):
        if start is None or stop is None:
            if kwargs.get('positive'):
                stop = S.Infinity
                start = S.Zero
                kwargs['left_open'] = True
            elif kwargs.get('nonnegative'):
                start = S.Zero
                stop = S.Infinity
            elif kwargs.get('negative'):
                start = S.NegativeInfinity
                stop = S.Zero
                kwargs['right_open'] = True
            elif kwargs.get('nonpositive'):
                start = S.NegativeInfinity
                stop = S.Zero
            else:
                start = S.NegativeInfinity
                stop = S.Infinity
        else:
            start = _sympify(start)
            stop = _sympify(stop)
        
        if 'left_open' in kwargs:
            left_open = kwargs['left_open']
        else:
            # by default, infinite interval start points are open.
            if start == S.NegativeInfinity:
                left_open = True
            else:
                left_open = False
            
        if 'right_open' in kwargs:
            right_open = kwargs['right_open']
        else:
            # by default, infinite interval stop points are open.
            if stop == S.Infinity:
                right_open = True
            else:
                right_open = False
            
        # evaluate if possible
        if right_open and stop <= start or not right_open and stop < start:
            return start.emptySet

        if stop == start:
            if left_open or right_open:
                return start.emptySet
            else:
                return FiniteSet(stop)

        infinitesimal = start.infinitesimality
        if infinitesimal is True:
            start = start.clear_infinitesimal()[0]
            left_open = True

        infinitesimal = stop.infinitesimality
        if infinitesimal is False:
            stop = stop.clear_infinitesimal()[0]
            right_open = True

        self = Basic.__new__(cls, start, stop)
        self.left_open = bool(left_open)
        self.right_open = bool(right_open)
        return self

    def element_symbol(self, excludes=set()):
        return self.generate_var(excludes, **self.etype.dict)

    @property
    def size(self):
        if self.etype.is_integer:
            if self.left_open:
                start = self.start + 1
            else:
                start = self.start
            if self.right_open:
                stop = self.stop
            else:
                stop = self.stop + 1
            return stop - start
        else:
            return self.stop - self.start

    def _eval_Card(self):
        ...

    @property
    def start(self):
        """
        The left end point of 'self'.

        This property takes the same value as the 'inf' property.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 1).start
        0

        """
        return self._args[0]

    _inf = left = start

    @classmethod
    def open(cls, a, b):
        """Return an interval including neither boundary."""
        return cls(a, b, left_open=True, right_open=True)

    @classmethod
    def Lopen(cls, a, b):
        """Return an interval not including the left boundary."""
        return cls(a, b, left_open=True, right_open=False)

    @classmethod
    def Ropen(cls, a, b):
        """Return an interval not including the right boundary."""
        return cls(a, b, left_open=False, right_open=True)

    @property
    def stop(self):
        """
        The right end point of 'self'.

        This property takes the same value as the 'sup' property.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 1).stop
        1

        """
        return self._args[1]

    _sup = right = stop

#     trying to evaluate other - self
    def _complement(self, other):
        if other.is_Interval and other.start.is_infinite and other.stop.is_infinite:
            a = Interval(S.NegativeInfinity, self.start, left_open=other.left_open, right_open=not self.left_open)
            b = Interval(self.stop, S.Infinity, left_open=not self.right_open, right_open=other.right_open)
            return a | b
        
        from sympy.sets import Integers
        if other == Integers:
            start, stop = S.NegativeInfinity, self.start
            if self.left_open:
                stop += 1
            from sympy import Range
            a = Range(start, stop)
            
            start, stop = self.stop, S.Infinity
            if not self.right_open:
                start += 1
            b = Range(start, stop)
            return a | b

        if other.is_FiniteSet:
            nums = [m for m in other.args if m.is_number]
            if nums == []:
                return

        return Set._complement(self, other)

    @property
    def _boundary(self):
        from sympy import FiniteSet
        finite_points = [p for p in (self.start, self.stop) if abs(p) != S.Infinity]
        return FiniteSet(*finite_points)

    def _contains(self, other):
        if not isinstance(other, Expr) or other is S.NaN or other is S.ComplexInfinity or other.is_extended_real == False:
            return S.false

        if other.is_Infinity:
            if not self.stop.is_Infinity or self.right_open:
                return S.false
                
        if other.is_NegativeInfinity:
            if not self.start.is_NegativeInfinity or self.left_open:
                return S.false
            
        if self.start is S.NegativeInfinity and self.stop is S.Infinity:
            if self.left_open:
                if self.right_open:
                    # self = (-oo, oo)
                    if other.is_real:
                        return S.true
                else:
                    # self = (-oo, oo]
                    if other.is_nonpositive or other.is_extended_positive:
                        return S.true
            else:
                if self.right_open:
                    # self = [-oo, oo)
                    if other.is_nonnegative or other.is_extended_negative:
                        return S.true
                else:
                    # self = [-oo, oo]
                    if other.is_extended_real:
                        return S.true

        if other.is_extended_real == False:
            return S.false
        
        if other.is_extended_real is None:
            return
        
        if self.left_open:
            expr = other > self.start
        else:
            expr = other >= self.start

        if self.right_open:
            expr = And(expr, other < self.stop)
        else:
            expr = And(expr, other <= self.stop)

        return _sympify(expr)

    @property
    def _measure(self):
        return self.stop - self.start

    def doit(self, deep=False, **_):
        if deep:
            return self.copy(start=self.start.doit(), stop=self.stop.doit())
        return self

    def to_mpi(self, prec=53):
        return mpi(mpf(self.start._eval_evalf(prec)),
            mpf(self.stop._eval_evalf(prec)))

    def _eval_evalf(self, prec):
        return Interval(self.left._eval_evalf(prec), self.right._eval_evalf(prec),
                        left_open=self.left_open, right_open=self.right_open)

    def _is_comparable(self, other):
        is_comparable = self.start.is_comparable
        is_comparable &= self.stop.is_comparable
        is_comparable &= other.start.is_comparable
        is_comparable &= other.stop.is_comparable

        return is_comparable

    @property
    def is_left_unbounded(self):
        """Return ``True`` if the left endpoint is negative infinity. """
        from sympy.core.numbers import Float
        return self.left is S.NegativeInfinity or self.left == Float("-inf")

    @property
    def is_right_unbounded(self):
        """Return ``True`` if the right endpoint is positive infinity. """
        from sympy.core.numbers import Float
        return self.right is S.Infinity or self.right == Float("+inf")

    def as_relational(self, x):
        """Rewrite an interval in terms of inequalities and logic operators."""
        x = sympify(x)
        if self.right_open:
            right = x < self.stop
        else:
            right = x <= self.stop
        if self.left_open:
            left = self.start < x
        else:
            left = self.start <= x
        return And(left, right)

    def _eval_Eq(self, other):
        if not other.is_Interval:
            if other.is_FiniteSet:
                if other.is_EmptySet:
                    if self.left_open or self.right_open:
                        if self.start < self.stop:
                            return S.false
                    else:
                        if self.start <= self.stop:
                            return S.false
                return
            elif other.is_set:
                return
            return S.false

        return And(Eq(self.left, other.left), Eq(self.right, other.right),
                   sympify(self.left_open == other.left_open), sympify(self.right_open == other.right_open))

    @cacheit
    def _eval_free_symbols(self):
        return set().union(*[a.free_symbols for a in self.args[:2]])

    def max(self):
        if self.right_open:
            from sympy.core.numbers import Infinity
            if isinstance(self.stop, Infinity):
                return self.stop
            # negative infinitesimal
            return self.stop + S.NegativeInfinitesimal
        return self.stop

    def min(self):
        if self.left_open:
            from sympy.core.numbers import NegativeInfinity
            if isinstance(self.start, NegativeInfinity):
                return self.start
            # positive infinitesimal
            return self.start + S.Infinitesimal
        return self.start

    def __neg__(self): 
        return self.func(-self.stop, -self.start, left_open=self.right_open, right_open=self.left_open)
    
    def __sub__(self, other):
        global is_set
        if not is_set(other):
            return self + (-other)
        return Set.__sub__(self, other)
    
    def __add__(self, other):
        other = sympify(other)
        if other.is_Interval:
            integer = None
            start = self.start
            stop = self.stop
            if other.etype.is_integer:
                start += other.min()
                stop += other.max()
                left_open, right_open = self.left_open, self.right_open
            else:
                start += other.start
                stop += other.stop
                
                if other.start.is_infinite and not other.left_open:
                    left_open = False
                else:
                    left_open = self.left_open or other.left_open
                    
                if other.stop.is_infinite and not other.right_open:
                    right_open = False
                else:
                    right_open = self.right_open or other.right_open
                
            return self.func(start, stop, left_open=left_open, right_open=right_open)
        
        if other.is_ComplexRegion:
            productset = other.args[0].args
            return other.func((self + productset[0]) @ productset[1])
        
        if other.is_FiniteSet:
            left_open, right_open = self.left_open, self.right_open
            start, stop = self.start, self.stop
            start += other.min()
            stop += other.max()                  
            return self.func(start, stop, left_open=left_open, right_open=right_open)
            
        if not other.is_set:
            start = self.start + other
            stop = self.stop + other
            return self.func(start, stop, left_open=self.left_open, right_open=self.right_open)

        if other.is_Range: 
            start = self.start
            stop = self.stop
            
            start += other.min()
            stop += other.max()
            left_open, right_open = self.left_open, self.right_open
                
            return self.func(start, stop, left_open=left_open, right_open=right_open)
        
        if other.is_UniversalSet and (other.etype.is_super_real or other.etype.is_super_complex):
            return other

        return Set.__add__(self, other)

    def __mul__(self, other):
        if isinstance(other, Expr):
            start = self.start * other
            stop = self.stop * other
            if other > 0:
                return self.func(start, stop, left_open=self.left_open, right_open=self.right_open)
            if other < 0:
                return self.func(stop, start, left_open=self.right_open, right_open=self.left_open)
            if other == 0:
                from sympy import FiniteSet
                return FiniteSet(0)
            return self.func(S.NegativeInfinity, S.Infinity)

        return Set.__mul__(self, other)

    def cos(self):
        from sympy.core.numbers import epsilon
        start, stop = self.args
        if self.right_open:
            stop -= epsilon

        from sympy import cos, floor

        n = floor(start / S.Pi)

        m = floor(stop / S.Pi)

        if n.is_even:
            if n == m:
                return self.func(cos(self.stop), cos(start),
                                 left_open=self.right_open,
                                 right_open=self.left_open)
        elif n.is_odd:
            if n == m:
                return self.copy(start=cos(start), stop=cos(self.stop))

        return self.func(-1, 1)

    def acos(self):
        from sympy import acos

        start, stop = self.args

        return self.func(acos(stop), acos(start), left_open=self.right_open, right_open=self.left_open)

    def __truediv__(self, other):
        if other.is_extended_positive: 
            return self.copy(start=self.start / other, stop=self.stop / other)
        if other.is_extended_negative: 
            return self.func(self.stop / other, self.start / other,
                             left_open=self.right_open, right_open=self.left_open)

    @cacheit
    def _has(self, pattern):
        return self.start._has(pattern) or self.stop._has(pattern)

    def copy(self, **kwargs):
        if 'start' in kwargs:
            start = kwargs['start']
        else:
            start = self.start

        if 'stop' in kwargs:
            stop = kwargs['stop']
        else:
            stop = self.stop
            
        if 'left_open' in kwargs:
            left_open = kwargs['left_open']
        else:
            left_open = self.left_open

        if 'right_open' in kwargs:
            right_open = kwargs['right_open']
        else:
            right_open = self.right_open
            
        if kwargs.get('integer'):
            from sympy import Range
            return Range(start, stop, left_open=left_open, right_open=right_open)
        
        return self.func(start, stop, left_open=left_open, right_open=right_open)

    def retain_odd(self):
        i = self.generate_var(integer=True)
        a, b = self.min(), self.max()
        if a.is_finite:
            a = (a / 2).floor()
        if b.is_finite:
            b = ((b - 1) / 2).floor()
            
        if a.is_infinite and b.is_infinite:
            domain = self
        else:
            domain = self.func(a, b, integer=True)
        from sympy import Cup
        return Cup[i:domain]((2 * i + 1).set)
        
    def retain_even(self):
        i = self.generate_var(integer=True)
        a, b = self.min(), self.max()
        if a.is_finite:
            a = (a / 2).floor()
        if b.is_finite:
            b = (b / 2).floor()
            
        if a.is_infinite and b.is_infinite:
            domain = self
        else:
            domain = self.func(a, b, integer=True)
        from sympy import Cup
        return Cup[i:domain]((2 * i).set)
        
    def _subs(self, old, new, **hints):
        assert old != new
        if self == old:
            return new
        
        hit = False
        args = list(self.args[:2])
        for i, arg in enumerate(args):
            if not hasattr(arg, '_eval_subs'):
                continue
            arg = arg._subs(old, new, **hints)
            if arg != args[i]:
                hit = True
                args[i] = arg
        if hit:
            start, stop = args
            return self.copy(start=start, stop=stop)
        return self

    @property
    def etype(self):
        if self.start.is_infinite and not self.left_open or self.stop.is_infinite and not self.right_open:
            return dtype.extended_real
        return dtype.real

    def _pretty(self, p): 
        if self.start == self.stop:
            return p._print_seq(self.args[:1], '{', '}')

        else:
            if self.left_open:
                left = '('
            else:
                left = '['

            if self.right_open:
                right = ')'
            else:
                right = ']'

            return p._print_seq(self.args[:2], left, right, delimiter=', ')

    def _sympystr(self, _):
        if self.left_open:
            if self.right_open:
                format = "Interval.open" 
            else:
                format = "Interval.Lopen"

                if self.stop is S.Infinity:
                    return "Interval(%s, %s, right_open=False)" % (self.start, self.stop)
        else:
            if self.right_open:
                format = "Interval.Ropen"
            else:
                format = "Interval"

                if self.start is S.NegativeInfinity:
                    if self.stop is S.Infinity:
                        return "Interval(%s, %s, left_open=False, right_open=False)" % (self.start, self.stop)
                    else:
                        return "Interval(%s, %s, left_open=False)" % (self.start, self.stop)
            
        return (format + "(%s, %s)") % (self.start, self.stop)

    def _lean(self, p):
        from sympy import Function
        if self.left_open:
            if self.right_open:
                if self.start is S.NegativeInfinity:
                    if self.stop is S.Infinity:
                        return "Set ℝ.univ"
                    else:
                        return Function.lean_fun('Iio', self.stop, p=p)
                else:
                    format = "Ioo" 
                    if self.stop is S.Infinity:
                        return Function.lean_fun('Ioi', self.start, p=p)
            else:
                format = "Ioc"
        else:
            if self.right_open:
                format = "Ico"
                if self.stop is S.Infinity:
                    return Function.lean_fun('Ici', self.start, p=p)
            else:
                format = "Icc"
        return Function.lean_fun(format, self.start, self.stop, p=p)

    def handle_finite_sets(self, unk):
        if all(arg.domain in self for arg in unk.args):
            return unk

    def _hashable_content(self):
        """Return a tuple of information about self that can be used to
        compute the hash. If a class defines additional attributes,
        like ``name`` in Symbol, then this method should be updated
        accordingly to return such relevant attributes.

        Defining more than _hashable_content is necessary if __eq__ has
        been defined by a class. See note about this in Basic.__eq__."""

        return self._args + (self.left_open, self.right_open)

    def _eval_is_extended_rational(self):
        ...
    
    def _eval_is_extended_real(self):
        return True
        
    def _eval_is_extended_complex(self):
        return True

    def _eval_is_super_real(self):
        return True

    def _eval_is_hyper_real(self):
        return True
    
    def _eval_is_extended_negative(self):
        if self.min().is_extended_nonnegative:
            return False
        if self.max().is_extended_negative:
            return True

    def _eval_is_extended_positive(self):
        if self.max().is_extended_nonpositive:
            return False
        if self.min().is_extended_positive:
            return True

    def _eval_is_zero(self):
        if self.min().is_extended_positive:
            return False
        if self.max().is_extended_negative:
            return False

    def _eval_is_empty(self):
        start, stop = self.args
        if start < stop:
            return False

    def _latex(self, p):
        if self.start == self.stop:
            return r"\left\{%s\right\}" % self._print(self.start)
        elif self.start.is_NegativeInfinity:
            if self.stop.is_Infinity:
                if self.left_open and self.right_open: 
                    return r"\mathbb{R}"
                
            elif self.stop.is_Zero:
                if self.left_open and self.right_open:
                    return r"\mathbb{R}^-"
                                    
        elif self.stop.is_Infinity:
            if self.start.is_Zero:
                if self.left_open and self.right_open:
                    return r"\mathbb{R}^+"
        
        if self.left_open:
            left = '('
        else:
            left = '['

        if self.right_open:
            right = ')'
        else:
            right = ']'

        return r"\left%s%s, %s\right%s" % (left, p._print(self.start), p._print(self.stop), right)

    @classmethod
    def simplify_Element(cls, self, e, s): 
        if s.start.is_NegativeInfinity:
            from sympy import Less, LessEqual
            func = Less if s.right_open else LessEqual
            if not s.left_open ^ bool(e.is_finite):
                return func(e, s.stop).simplify()
            
        if s.stop.is_Infinity:
            from sympy import Greater, GreaterEqual
            func = Greater if s.left_open else GreaterEqual
            if not s.right_open ^ bool(e.is_finite):
                return func(e, s.start).simplify()
        
        finiteset = e.domain - s
        if finiteset.is_FiniteSet:
            return self.invert_type(e, finiteset).simplify()
            
    @classmethod
    def simplify_NotElement(cls, self, e, s):
        if e.is_real:
            if s.stop.is_infinite:
                if s.left_open:
                    return e <= s.start
                else:
                    return e < s.start
            elif s.start.is_infinite:
                if s.right_open:
                    return e >= s.start
                else:
                    return e > s.start

# perform self in rhs
    def _eval_Subset(self, rhs):
        if rhs.is_UniversalSet:
            return S.true
        if rhs.is_Interval:
            if self.left_open == rhs.left_open:
                if rhs.start == self.start:
                    if self.right_open == rhs.right_open or self.right_open and not rhs.right_open:
                        if self.stop <= rhs.stop:
                            return S.true
            if self.right_open == rhs.right_open:
                if rhs.stop == self.stop:
                    if self.left_open == rhs.left_open or self.left_open and not rhs.left_open:
                        if self.start >= rhs.start:
                            return S.true

    @property
    def kwargs(self):
        return {'left_open': self.left_open, 'right_open': self.right_open}             
      
    @property
    def kwargs_reversed(self):
        return {'left_open': self.right_open, 'right_open': self.left_open}

    @classmethod
    def assume(cls, **kwargs):
        left_open = False
        right_open = False
        if kwargs.get('positive'):
            stop = S.Infinity
            start = S.Zero
            left_open = True
        elif kwargs.get('nonnegative'):
            start = S.Zero
            stop = S.Infinity
        elif kwargs.get('negative'):
            start = S.NegativeInfinity
            stop = S.Zero
            right_open = True
        elif kwargs.get('nonpositive'):
            start = S.NegativeInfinity
            stop = S.Zero
        else:
            start = S.NegativeInfinity
            stop = S.Infinity
        return cls(start, stop, left_open=left_open, right_open=right_open)
        
    def adjust_domain(self, x, *cond):
        if self.start._has(x):
            self = self.copy(start=S.NegativeInfinity)
                    
        if self.stop._has(x):
            self = self.copy(stop=S.Infinity)
            
        return self

    def conditionally_contains(self, ft):
        a, b = self.args
        if self.left_open:
            if self.right_open:
                if a < ft < b:
                    return True
            else:
                if a < ft <= b:
                    return True
        else:
            if self.right_open:
                if a <= ft < b:
                    return True
            else:
                if a <= ft <= b:
                    return True

        free_symbols = ft.free_symbols
        if len(free_symbols) == 1:
            t, = free_symbols
            if not t.shape:
                cond = b - a > 0
                if cond._has(t):
                    _t = t.copy(domain=cond.domain_conditioned(t))
                    
                a_ = a._subs(t, _t)
                ft_ = ft._subs(t, _t)
                b_ = b._subs(t, _t)
                
                if self.left_open:
                    if self.right_open:
                        if a_ < ft_ < b_:
                            return True
                    else:
                        if a_ < ft_ <= b_:
                            return True
                else:
                    if self.right_open:
                        if a_ <= ft_ < b_:
                            return True
                    else:
                        if a_ <= ft_ <= b_:
                            return True
                    
        # given: a < b
        # imply: a < t < b
        fa = (ft - a) / (b - a)
        fa = fa.ratsimp()
        if self.left_open and fa > 0 or not self.left_open and fa >= 0: 
            fb = (ft - b) / (b - a)
            fb = fb.ratsimp()
            if self.right_open and fb < 0 or not self.right_open and fb <= 0:
                return True

    def _eval_is_finiteset(self):
        a, b = self.args
        if a < b:
            return False

    @property
    def is_closed(self):
        return not self.left_open and not self.right_open
    
    @property
    def is_open(self):
        return self.left_open and self.right_open

    @cacheit
    def sort_key(self, order=None):
        args = self._sorted_args
        args = len(args), tuple(arg.class_key() for arg in args), tuple(arg.sort_key(order=order) for arg in args)
        left_closed = int(not self.left_open)
        right_closed = int(not self.right_open)
        return (*self.class_key(), left_closed, right_closed), args, S.One.sort_key(), S.One


class Union(Set, LatticeOp, EvalfMixin):
    """
    Represents a union of sets as a :class:`Set`.

    Examples
    ========

    >>> from sympy import Union, Interval
    >>> Union(Interval(1, 2), Interval(3, 4))
    Union(Interval(1, 2), Interval(3, 4))

    The Union constructor will always try to merge overlapping intervals,
    if possible. For example:

    >>> Union(Interval(1, 2), Interval(2, 3))
    Interval(1, 3)

    See Also
    ========

    Intersection

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Union_%28set_theory%29
    """

    def __new__(cls, *args, **kwargs):
        evaluate = kwargs.get('evaluate', global_parameters.evaluate)

        # flatten inputs to merge intersections and iterables
        [*args] = map(_sympify, args)
        if len(args) == 1:
            return args[0]
        # Reduce sets using known rules
        if evaluate:
            args = list(cls._new_args_filter(args))
            return simplify_union(args)

        args.sort(key=lambda arg: arg.sort_key())

        obj = Basic.__new__(cls, *args)
        obj._argset = frozenset(args)
        return obj

    @classmethod
    def _new_args_filter(cls, arg_sequence, call_cls=None):
        """Generator filtering args"""
        ncls = call_cls or cls
        for arg in arg_sequence: 
            if arg.func == ncls:
                yield from arg.args
            else:
                yield arg

    def _complement(self, universe):
        # DeMorgan's Law
        return Intersection(s.complement(universe) for s in self.args)

    @property
    def _inf(self):
        # We use Min so that sup is meaningful in combination with symbolic
        # interval end points.
        from sympy.functions.elementary.miscellaneous import Min
        return Min(*[s.inf for s in self.args])

    @property
    def _sup(self):
        # We use Max so that sup is meaningful in combination with symbolic
        # end points.
        from sympy.functions.elementary.miscellaneous import Max
        return Max(*[s.sup for s in self.args])

    def _contains(self, other):
        return Or(*[Element(other, s) for s in self.args])

    @property
    def _measure(self):
        # Measure of a union is the sum of the measures of the sets minus
        # the sum of their pairwise intersections plus the sum of their
        # triple-wise intersections minus ... etc...

        # Sets is a collection of intersections and a set of elementary
        # sets which made up those intersections (called "sos" for set of sets)
        # An example element might of this list might be:
        #    ( {A,B,C}, A.intersect(B).intersect(C) )

        # Start with just elementary sets (  ({A}, A), ({B}, B), ... )
        # Then get and subtract (  ({A,B}, (A int B), ... ) while non-zero
        from sympy import FiniteSet
        sets = [(FiniteSet(s), s) for s in self.args]
        measure = 0
        parity = 1
        while sets:
            # Add up the measure of these sets and add or subtract it to total
            measure += parity * sum(inter.measure for sos, inter in sets)

            # For each intersection in sets, compute the intersection with every
            # other set not already part of the intersection.
            sets = ((sos + FiniteSet(newset), newset.intersect(intersection))
                    for sos, intersection in sets for newset in self.args
                    if newset not in sos)

            # Clear out sets with no measure
            sets = [(sos, inter) for sos, inter in sets if inter.measure != 0]

            # Clear out duplicates
            sos_list = []
            sets_list = []
            for s in sets:
                if s[0] in sos_list:
                    continue
                else:
                    sos_list.append(s[0])
                    sets_list.append(s)
            sets = sets_list

            # Flip Parity - next time subtract/add if we added/subtracted here
            parity *= -1
        return measure

    @property
    def _boundary(self):

        def boundary_of_set(i):
            """ The boundary of set i minus interior of all other sets """
            b = self.args[i].boundary
            for j, a in enumerate(self.args):
                if j != i:
                    b = b - a.interior
            return b

        return Union(*map(boundary_of_set, range(len(self.args))))

    def as_relational(self, symbol):
        """Rewrite a Union in terms of equalities and logic operators. """
        if len(self.args) == 2:
            a, b = self.args
            if (a.sup == b.inf and a.inf is S.NegativeInfinity
                    and b.sup is S.Infinity):
                return And(Ne(symbol, a.sup), symbol < b.sup, symbol > a.inf)
        return Or(*[s.as_relational(symbol) for s in self.args])

    @property
    def is_iterable(self):
        return all(arg.is_iterable for arg in self.args)

    def _eval_evalf(self, prec):
        try:
            return Union(*(s._eval_evalf(prec) for s in self.args))
        except (TypeError, ValueError, NotImplementedError):
            import sys
            raise (TypeError("Not all sets are evalf-able"),
                   None,
                   sys.exc_info()[2])

    def __iter__(self):
        import itertools

        # roundrobin recipe taken from itertools documentation:
        # https://docs.python.org/2/library/itertools.html#recipes
        def roundrobin(*iterables):
            "roundrobin('ABC', 'D', 'EF') --> A D E B F C"
            # Recipe credited to George Sakkis
            pending = len(iterables)
            if PY3:
                nexts = itertools.cycle(iter(it).__next__ for it in iterables)
            else:
                nexts = itertools.cycle(iter(it).next for it in iterables)
            while pending:
                try:
                    for next in nexts:
                        yield next()
                except StopIteration:
                    pending -= 1
                    nexts = itertools.cycle(itertools.islice(nexts, pending))

        if all(s.is_iterable for s in self.args):
            return roundrobin(*(iter(arg) for arg in self.args))
        else:
            raise TypeError("Not all constituent sets are iterable")

    def _eval_is_finiteset(self):
        if fuzzy_et(a.is_finiteset for a in self.args):
            return True

    def _eval_is_extended_integer(self):
        return fuzzy_et(arg.is_extended_integer for arg in self.args)

    def _eval_is_super_integer(self):
        return fuzzy_et(e.is_super_integer for e in self.args)
    
    def _eval_is_extended_rational(self):
        return fuzzy_et(e.is_extended_rational for e in self.args)
    
    def _eval_is_super_rational(self):
        return fuzzy_et(e.is_super_rational for e in self.args)

    def _eval_is_hyper_rational(self):
        return fuzzy_et(e.is_hyper_rational for e in self.args)
    
    def _eval_is_extended_real(self):
        return fuzzy_et(e.is_extended_real for e in self.args) 

    def _eval_is_hyper_real(self):
        return fuzzy_et(e.is_hyper_real for e in self.args)
    
    def _eval_is_super_real(self):
        return fuzzy_et(e.is_super_real for e in self.args)
    
    def _eval_is_extended_complex(self):
        return fuzzy_et(e.is_extended_complex for e in self.args)
     
    def _eval_is_hyper_complex(self):
        return fuzzy_et(e.is_hyper_complex for e in self.args)

    @property
    def etype(self):
        dtype = None
        for e in self.args:
            _dtype = e.etype
            if dtype is None:
                dtype = _dtype
                continue
            if dtype != _dtype:
                if _dtype in dtype:
                    continue
                if dtype in _dtype:
                    dtype = _dtype
                    continue
                raise Exception('inconsistent dtype: %s and %s' % (dtype, _dtype))

        return dtype

    def _eval_Card(self):
        non_intersect = []
        args = [*self.args]
        for A in self.args:
            intersect = False
            for B in args:
                if A == B:
                    continue

                if A & B:
                    intersect = True
                    break
            if intersect:
                continue
            non_intersect.append(A)
            args.remove(A)

        if non_intersect:
            from sympy import Add, Card
            if args:
                s = Card(Union(*args))
            else:
                s = 0
            return Add(*[Card(A) for A in non_intersect]) + s

    def min(self):
        from sympy.functions.elementary.miscellaneous import Min
        return Min(*(arg.min() for arg in self.args))        

    def max(self):
        from sympy.functions.elementary.miscellaneous import Max
        return Max(*(arg.max() for arg in self.args))        

    def _sympystr(self, p):
        return ' | '.join(["(%s)" % p._print(a) if a.is_Complement else p._print(a) for a in self.args])

    def _lean(self, p):
        return ' \N{UNION} '.join(["(%s)" % p._print(a) if a.is_Complement else p._print(a) for a in self.args])

    def _latex(self, p):
        args = []
        for i in self.args:
            latex = p._print(i)
            if i.is_Complement or i.is_Union:
                latex = r'\left(%s\right)' % latex
            args.append(latex)

        return r" \cup ".join(args)

    def __add__(self, other):
        if other.is_set:
            raise Exception("could not add %s, %s" % (self, other))
        return self.func(*(arg + other for arg in self.args))

    # perform lhs in self
    def _eval_Subset_reversed(self, lhs):
        if lhs in self._argset:
            return S.true

    # perform self in rhs
    def _eval_Subset(self, rhs):
        from sympy import Subset
        for s in self._argset: 
            cond = Subset(s, rhs)
            if cond:
                continue
            elif cond == False:
                return S.false
            else:
                return
        return S.true

    def simplify(self, deep=False, **kwargs):
        if deep:
            return Set.simplify(self, deep=deep, **kwargs)
        return self

    def _subs(self, old, new, **hints):
        if old.is_Union:
            if not old._argset - self._argset:
                diff = self._argset - old._argset
                if diff:
                    return Union(*diff) | new
                return new
        return Set._subs(self, old, new, **hints)

    @classmethod
    def class_key(cls):
        """Nice order of classes. """
        return 5, 8, cls.__name__

    def toset(self):
        s = set()
        for arg in self.args:
            if arg.is_FiniteSet:
                s |= {*arg.args}
            else:
                s |= arg.toset()
            
        return s


class Intersection(Set, LatticeOp):
    """
    Represents an intersection of sets as a :class:`Set`.

    Examples
    ========

    >>> from sympy import Intersection, Interval
    >>> Intersection(Interval(1, 3), Interval(2, 4))
    Interval(2, 3)

    We often use the .intersect method

    >>> Interval(1,3).intersect(Interval(2,4))
    Interval(2, 3)

    See Also
    ========

    Union

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Intersection_%28set_theory%29
    """

    @property
    def etype(self):
        dtype = None
        for e in self.args:
            _dtype = e.etype
            if dtype is None:
                dtype = _dtype
                continue
            if dtype != _dtype:
                if _dtype in dtype:
                    continue
                if dtype in _dtype:
                    dtype = _dtype
                    continue
                raise Exception('inconsistent dtype: %s and %s' % (dtype, _dtype))

        return dtype

    def union_sets(self, b):
# (A - B) | (C & D) = ((A - B) | C) & ((A - B) | D) = (A | C) & ((A - B) | D)
        for i, c in enumerate(self.args):
            if c.is_subset(b):
                return b
            if c.is_Complement:
                A, B = c.args
                if B in b:
#                     ({k} & ([0; n) / {i})) | {i}
                    args = [*self.args]
                    del args[i]
                    return (self.func(*args, evaluate=False) | b) & A
            
# (A & C) | (B & C) = (A | B) & C
        if b.is_Intersection:
            C = self._argset & b._argset
            if C: 
                a_set = self._argset - C
                b_set = b._argset - C
                if not a_set or not b_set:
                    return self.func(*C)
                
                a_set = self.func(*a_set, evaluate=False)
                b_set = self.func(*b_set, evaluate=False)
                return Intersection(a_set | b_set, self.func(*C), evaluate=False)
        
    def __new__(cls, *args, **kwargs):
        evaluate = kwargs.get('evaluate', global_parameters.evaluate)

        # flatten inputs to merge intersections and iterables
        [*args] = map(_sympify, args)
        if len(args) == 1:
            return args[0]
        # Reduce sets using known rules
        if evaluate:
            args = list(cls._new_args_filter(args))
            return simplify_intersection(args)

        args.sort(key=lambda arg: arg.sort_key())

        obj = Basic.__new__(cls, *args)
        obj._argset = frozenset(args)
        return obj

    @classmethod
    def _new_args_filter(cls, arg_sequence, call_cls=None):
        """Generator filtering args"""
        ncls = call_cls or cls
        for arg in arg_sequence: 
            if arg.func == ncls:
                yield from arg.args
            else:
                yield arg

    @property
    def is_iterable(self):
        return any(arg.is_iterable for arg in self.args)

    @property
    def _inf(self):
        raise NotImplementedError()

    @property
    def _sup(self):
        raise NotImplementedError()

    def _contains(self, other):
        return And(*[Element(other, s) for s in self.args])

    def __iter__(self):
        no_iter = True
        for s in self.args:
            if s.is_iterable:
                no_iter = False
                other_sets = set(self.args) - set((s,))
                other = Intersection(*other_sets, evaluate=False)
                for x in s:
                    c = sympify(other.contains(x))
                    if c is S.true:
                        yield x
                    elif c is S.false:
                        pass
                    else:
                        yield c

        if no_iter:
            raise ValueError("None of the constituent sets are iterable")

    @staticmethod
    def _handle_finite_sets(args):
        from itertools import zip_longest

        fs_args, other = sift(args, lambda x: x.is_FiniteSet, binary=True)
        if not fs_args:
            return
        fs_args.sort(key=len)
        s = fs_args[0]
        fs_args = fs_args[1:]

        res = []
        unk = []
        for x in s:
            c = fuzzy_and(fuzzy_bool(o.contains(x)) for o in fs_args + other)
            if c:
                res.append(x)
            elif c is None:
                unk.append(x)
            else:
                pass  # drop arg
            
        from sympy import FiniteSet
        res = FiniteSet(*res) if res else s.emptySet
        if unk:
            symbolic_s_list = [x for x in s if x.has(Symbol)]
            while fs_args:
                v = fs_args.pop()
                if not all(i == j for i, j in zip_longest(symbolic_s_list, (x for x in v if x.has(Symbol)))):
                    # if only a subset of elements in `s` are
                    # contained in `v` then remove them from `v`
                    # and add this as a new arg
                    contained = [x for x in symbolic_s_list if sympify(v.contains(x)) is S.true]
                    if contained != symbolic_s_list:
                        other.append(Complement(v, FiniteSet(*contained)))
                    else:
                        other.append(v)

            other_sets = Intersection(*other)
            if not other_sets:
                return s.emptySet  # b/c we use evaluate=False below
            elif other_sets.is_UniversalSet:
                res |= FiniteSet(*unk)
            else:
                unk = FiniteSet(*unk)
                result = other_sets.handle_finite_sets(unk)
                if result is not None:
                    return res | result
                return res | Intersection(unk, other_sets, evaluate=False) 
        return res

    def as_relational(self, symbol):
        """Rewrite an Intersection in terms of equalities and logic operators"""
        return And(*[s.as_relational(symbol) for s in self.args])

    """
    precondition: this set should not be empty!
    """

    def min(self):
        from sympy.functions.elementary.miscellaneous import Max
        return Max(*(arg.min() for arg in self.args))        

    """
    precondition: this set should not be empty!
    """

    def max(self):
        from sympy.functions.elementary.miscellaneous import Min
        return Min(*(arg.max() for arg in self.args))

    def _sympystr(self, p):
        args = ["(%s)" % p._print(a) if a.is_Complement or a.is_Union else p._print(a) for a in self.args]
        if self.args[0].is_FiniteSet:
            if self.args[1].is_FiniteSet:
                args[0] = 'FiniteSet(%s)' % args[0][1:-1]

        return ' & '.join(args)

    def _lean(self, p):
        args = ["(%s)" % p._print(a) if a.is_Complement or a.is_Union else p._print(a) for a in self.args]
        if self.args[0].is_FiniteSet:
            if self.args[1].is_FiniteSet:
                args[0] = '{%s}' % args[0][1:-1]

        return ' \N{INTERSECTION} '.join(args)

    def _latex(self, p):
        args = []
        for i in self.args:
            latex = p._print(i)
            if i.is_Complement or i.is_Union:
                latex = r'\left(%s\right)' % latex
            args.append(latex)

        return r" \cap ".join(args)

    def handle_finite_sets(self, unk):
        for i, s in enumerate(self.args):
            if unk in s:
                args = [*self.args]
                args[i] = unk
                return self.func(*args, evaluate=False)
            if s in unk:
                return self
        return self.func(*self.args, unk, evaluate=False)

    def _eval_is_finiteset(self):
        return fuzzy_ou(a.is_finiteset for a in self.args)
        
    def _eval_is_extended_integer(self):
        return fuzzy_ou(arg.is_extended_integer for arg in self.args)

    def _eval_is_super_integer(self):
        return fuzzy_ou(e.is_super_integer for e in self.args)
    
    def _eval_is_extended_rational(self):
        return fuzzy_ou(e.is_extended_rational for e in self.args)
    
    def _eval_is_super_rational(self):
        return fuzzy_ou(e.is_super_rational for e in self.args)

    def _eval_is_hyper_rational(self):
        return fuzzy_ou(e.is_hyper_rational for e in self.args)
    
    def _eval_is_extended_real(self):
        return fuzzy_ou(e.is_extended_real for e in self.args) 

    def _eval_is_hyper_real(self):
        return fuzzy_ou(e.is_hyper_real for e in self.args)
    
    def _eval_is_super_real(self):
        return fuzzy_ou(e.is_super_real for e in self.args)
    
    def _eval_is_extended_complex(self):
        return fuzzy_ou(e.is_extended_complex for e in self.args)
     
    def _eval_is_hyper_complex(self):
        return fuzzy_ou(e.is_hyper_complex for e in self.args)
            
    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a Intersection object!
        """
        if rhs.is_EmptySet:
            this = self.simplify_Intersection(lhs)
            if this is not None:
                return this

    def __add__(self, other):
        if other.is_set:
            raise Exception("could not add %s, %s" % (self, other))
        return self.func(*(arg + other for arg in self.args))

    # perform self in rhs
    def _eval_Subset(self, rhs):
        for e in self._argset:
            if e in rhs:
                return S.true

    # perform lhs in self
    def _eval_Subset_reversed(self, lhs):
        from sympy import Subset
        for e in self._argset:
            cond = Subset(lhs, e)
            if cond:
                continue
            if cond == False:
                return S.false
            else:
                return
        return S.true

    def _subs(self, old, new, **hints):
        if old.is_Intersection:
            if not old._argset - self._argset:
                diff = self._argset - old._argset
                if diff:
                    return Intersection(*diff) & new
                return new
        return Set._subs(self, old, new, **hints)

    @classmethod
    def class_key(cls):
        """Nice order of classes. """
        return 5, 7, cls.__name__


class Complement(Set, EvalfMixin):
    r"""Represents the set difference or relative complement of a set with
    another set.

    `A - B = \{x \in A| x \\notin B\}`


    Examples
    ========

    >>> from sympy import Complement, FiniteSet
    >>> Complement(FiniteSet(0, 1, 2), FiniteSet(1))
    {0, 2}

    See Also
    =========

    Intersection, Union

    References
    ==========

    .. [1] http://mathworld.wolfram.com/ComplementSet.html
    """

    is_Complement = True

    def _latex(self, p):
        A, B = self.args
        if B.is_Complement:
            B = r"\left(%s\right)" % p._print(B)
        else:
            B = p._print(B)
            
        return r"%s \setminus %s" % (p._print(A), B)

    def _sympystr(self, p): 
        A, B = self.args
        if B.is_Complement or B.is_Intersection or B.is_Union:
            B = r"(%s)" % p._print(B)
        else:
            B = p._print(B)
            
        return r"%s - %s" % (p._print(A), B)

    def _lean(self, p): 
        A, B = self.args
        if B.is_Complement or B.is_Intersection or B.is_Union:
            B = r"(%s)" % p._print(B)
        else:
            B = p._print(B)
            
        return r"%s \ %s" % (p._print(A), B)

    def is_connected_interval(self): 
        A, B = self.args
        
        if not (A.is_Interval or A.is_Range):
            return False
        
        if B.is_Interval or B.is_Range:
            return True
            
        if not B.is_FiniteSet:
            return False
        
        if len(B) == 1:
            return True
        
        if not A.etype.is_integer:
            return False
        
        return B.etype.is_integer and B.max() - B.min() == len(B) - 1
        
    def min(self): 
        A, B = self.args
        x = A.min()
            
        if x.is_infinite:
            if Element(x, B) == False:
                return x
            
        if self.is_connected_interval():
            from sympy.core.numbers import epsilon
            from sympy import floor
            M = B.max()        
            if A.etype.is_integer: 
                M = floor(M) + 1
            else:
                M += epsilon
                
            from sympy.functions.elementary.piecewise import Piecewise
            return Piecewise((M, Element(x, B).simplify()), (x, True)).simplify()
        
        m = B.min()
        if x < m:
            return x
        
        from sympy.concrete.reduced import ReducedMin
        return ReducedMin(self)

    def max(self): 
        A, B = self.args
        x = A.max()      
          
        if x.is_infinite:
            if Element(x, B) == False:
                return x
        
        if self.is_connected_interval():
            from sympy.core.numbers import epsilon
            from sympy import ceil
            m = B.min()
            if A.etype.is_integer: 
                m = ceil(m) - 1
            else:
                m -= epsilon
                
            from sympy.functions.elementary.piecewise import Piecewise
            return Piecewise((m, Element(x, B).simplify()), (x, True)).simplify()
        
        M = B.max()
        if x > M:
            return x
        
        from sympy.concrete.reduced import ReducedMax
        return ReducedMax(self)  

    @property
    def etype(self):
        return self.args[0].etype

    def __new__(cls, a, b, evaluate=True):
        from sympy import FiniteSet
        if isinstance(b, set):
            b = FiniteSet(*b)

        if isinstance(a, set):
            a = FiniteSet(*a)

        if evaluate:
            return Complement.reduce(a, b)

        return Basic.__new__(cls, a, b)

# A - (B - (A & B)) = A
# A  &  (B - (A & B)) = 0
# (A & B)  &  (B - (A & B)) = 0
# A - (B - A & b), b in B
    def _complement(self, A):
        B, C = self.args
        if C.is_Intersection:
            args = [*C.args]
            try:
                index = args.index(A)
                del args[index]
                b = C.func(*args, evaluate=False)
                if b == B:
                    return A
                if b in B:
                    B = Complement(B, b)
                    return self.func(A, B, evaluate=False)
            except:
                return
        if A in B | C:
            return A & C
        if not A & C:
            return Complement(A, B)
        if B in A:
#             if C in B:
#                 return (A - B) | C
            if C in A:  # C in B => C in A
                return Complement(A, B) | C
#             return (A - B) | (B & C)

    @staticmethod
    def reduce(A, B):
        """
        Simplify a :class:`Complement`.

        """
        # try to evaluate A \ B
        if B.is_UniversalSet:
            if A.etype in B.etype:
                return A.etype.emptySet
        
        if A.is_subset(B):
            return A.etype.emptySet

        if B.is_Union:
            if A.is_Complement:
                if B in A.args[1]:
                    return A
                if A.args[1] in B:
                    return Complement(A.args[0], B, evaluate=False) 

            return Intersection(*(s.complement(A) for s in B.args))

        result = B._complement(A)
        if result is not None:
            return result

        if A.is_Union:
            for i, arg in enumerate(A.args):
                if arg in B:
                    args = [*A.args]
                    del args[i]
                    A = A.func(*args)
                    return Complement(A, B)
                 
        if A.is_Cup:
            if A.is_ConditionSet:
                if not B.is_ConditionSet:
                    from sympy.sets import conditionset
                    base_set = B._complement(A.base_set)
                    if base_set is not None:
                        if A.base_set == base_set:
                            return A
                        return conditionset(A.variable, A.condition, base_set)
            elif A.range_contains(B) is False:
                return A
                    
        if B.is_Intersection and A in B._argset:
            B = B.func(*B._argset - {A}, evaluate=False)
            
        if A.is_Piecewise:
            return A.func(*((Complement(e, B), c) for e, c in A.args)).simplify()
        
        if A.is_Intersection:
            for i, arg in enumerate(A.args):
                if arg.is_Complement and arg.args[1] in B: 
                    args = [*A.args]
                    args[i] = arg.args[0]
                    A = A.func(*args, evaluate=False)
                    return Complement(A, B)
                     
        if A.is_Complement:
            _A, _B = A.args
            if B in _B:
                return A
            A, B = _A, _B | B
        return Complement(A, B, evaluate=False)

    def _contains(self, other):
        A = self.args[0]
        B = self.args[1]
        return And(Element(other, A), Element(other, B).invert())

    def union_sets(self, C):
        A, B = self.args
        if B in C:
            return A | C
        if A in C:
            return C
        if C.is_Intersection:
            if A & B in C:
                return A | C
            try:
                # A & B | (A-B) = A
                # A & B | (A-(B+C)) = A - C
                args = [*C.args]
                index = args.index(A)
                del args[index]
                rest = C.func(*args, evaluate=False)
                if rest in B:
                    return Complement(A, Complement(B, rest))
            except:
                return
        if C in B:
            B = Complement(B, C)
            return self.func(A | C, B, evaluate=False)
        if C.is_Complement:
            _A, _B = C.args
            if B == _B:
                return Complement(A | _A, B)
            if _B in self:
                return _A | self

# if B => C, (A - B) | C = A | C
# if A => C, (A - B) | C = C

    def _eval_is_extended_integer(self):
        return self.args[0].is_extended_integer

    def _eval_is_super_integer(self):
        return self.args[0].is_super_integer
    
    def _eval_is_extended_rational(self):
        return self.args[0].is_extended_rational
    
    def _eval_is_hyper_rational(self):
        return self.args[0].is_hyper_rational
    
    def _eval_is_super_rational(self):
        return self.args[0].is_super_rational
    
    def _eval_is_extended_real(self):
        return self.args[0].is_extended_real
    
    def _eval_is_extended_negative(self):
        return self.args[0].is_extended_negative

    def _eval_is_extended_positive(self):
        return self.args[0].is_extended_positive
    
    def _eval_is_hyper_real(self):
        return self.args[0].is_hyper_real
    
    def _eval_is_super_real(self):
        return self.args[0].is_super_real
    
    def _eval_is_extended_complex(self):
        return self.args[0].is_extended_complex

    def _eval_is_zero(self):
        return self.args[0].is_zero

    def _eval_is_finiteset(self):
        return self.args[0].is_finiteset

    @cacheit
    def _eval_domain_defined(self, x, **_):
        A, B = self.args
        return A.domain_defined(x) & B.domain_defined(x)

    def supremum(self):
        return self.args[0].max()

    def infimum(self):
        return self.args[0].min()
    
    def __add__(self, other):
        A, B = self.args
        return self.func(A + other, B + other)
    
    def handle_finite_sets(self, unk):
        A, B = self.args
        intersection = unk & B
        if intersection == unk: #equivalently, unk in B
            return self.etype.emptySet
        
        if intersection.is_EmptySet:
            return A & unk

        if unk in A:
            if B.is_Intersection:
                args = []
                for s in B.args:
                    if unk in s:
                        continue
                    args.append(s)
                if len(args) != len(B.args):
                    B = B.func(*args)
                        
            return self.func(unk, B, evaluate=False)
        if A in unk:
#             consider the case : [0; n) & {j} / [0; n) & {i}, {j}
            return self

    @classmethod
    def simplify_Unequal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a Complement object!
        """
        if rhs.is_EmptySet:
            A, B = lhs.args
            from sympy import NotSubset
            return NotSubset(A, B).simplify()

    @classmethod
    def simplify_Element(cls, self, e, s):
        """
        precondition: self.rhs is a Complement object!
        """
        U, B = s.args
        if U.is_UniversalSet:
            return self.invert_type(e, B).simplify() 
        elif B.is_FiniteSet and len(B) == 1:
            _e, = B
            from sympy import Unequal
            ne = Unequal(e, _e)
            if ne:
                return Element(e, U)

            domain_assumed = e.domain_assumed
            if domain_assumed and domain_assumed == U:
                return ne

        elif e in U:
            from sympy import NotElement
            return NotElement(e, B)

    @classmethod
    def simplify_NotElement(cls, self, e, s):
        """
        precondition: self.rhs is a Complement object!
        """
        U, B = s.args
        if U.is_UniversalSet:
            return self.invert_type(e, B).simplify()
        elif B.is_FiniteSet and len(B) == 1:
            _e, = B
            eq = Equal(e, _e)
            if eq:
                return self.func(e, U)

            domain_assumed = e.domain_assumed
            if domain_assumed and domain_assumed == U:
                return eq

        elif e in U:
            from sympy import Element
            return Element(e, B)
        
    def _eval_Subset(self, rhs):
        A, s = self.args
        if rhs.is_Complement: 
            B, _s = rhs.args
            if s == _s:
                from sympy import Subset
                return Subset.eval(A, B)
        elif rhs == A:
            return S.BooleanTrue
            
    @classmethod
    def class_key(cls):
        """Nice order of classes. """
        return 5, 9, cls.__name__


class EmptySet(Set):
    """
    Represents the empty set. The empty set is available as a singleton
    as EmptySet().

    Examples
    ========

    >>> from sympy import S, Interval
    >>> EmptySet()
    EmptySet()

    >>> Interval(1, 2).intersect(EmptySet())
    EmptySet()

    See Also
    ========

    UniversalSet

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Empty_set
    """
    is_FiniteSet = True
    is_empty = True

    def _eval_is_extended_integer(self):
        return self.etype.is_extended_integer

    def _eval_is_super_integer(self):
        return self.etype.is_super_integer
    
    def _eval_is_extended_rational(self):
        return self.etype.is_extended_rational
    
    def _eval_is_hyper_rational(self):
        return self.etype.is_hyper_rational
    
    def _eval_is_super_rational(self):
        return self.etype.is_super_rational
    
    def _eval_is_extended_real(self):
        return self.etype.is_extended_real
    
    def _eval_is_hyper_real(self):
        return self.etype.is_hyper_real
    
    def _eval_is_super_real(self):
        return self.etype.is_super_real
    
    def _eval_is_extended_complex(self):
        return self.etype.is_extended_complex
    
    def _eval_is_hyper_complex(self):
        return self.etype.is_hyper_complex
    
    def _eval_is_finiteset(self):
        return True
    
    @property
    def etype(self):
        return self._assumptions['etype']

    def _eval_Card(self):
        return S.Zero

    def intersection_sets(self, b):
        return self

    def union_sets(self, b):
        return b

    @property
    def _measure(self):
        return 0

    def _contains(self, other):
        return S.false

    def as_relational(self, symbol):
        return S.false

    def __len__(self):
        return 0

    def __iter__(self):
        return iter([])

    def _eval_powerset(self):
        from sympy import FiniteSet
        return FiniteSet(self)

    @property
    def _boundary(self):
        return self

    def _complement(self, other):
        return other

    def _symmetric_difference(self, other):
        return other

    def _sympystr(self, _):
        return f'dtype.{self.etype}.emptySet'

    def _lean(self, _):
        return '\N{EMPTY SET}'
        # return '\N{LATIN CAPITAL LETTER O WITH STROKE}'

    def _latex(self, p):
        return r"\emptyset"

    def __add__(self, other):
        return self

    def __sub__(self, other):
        return self

    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a EmptySet object!
        """
        if rhs.is_Intersection:
            this = self.simplify_Intersection(rhs)
            if this is not None:
                return this

    def _eval_Subset(self, rhs):
        return S.true

    def _eval_Eq(self, rhs):
        if rhs.is_empty is False:
            return S.false
        
        if rhs.is_empty is True:
            return S.true

        
class UniversalSet(Set):
    """
    Represents the set of all things.
    The universal set is available as a singleton as UniversalSet()

    Examples
    ========

    >>> from sympy import S, Interval
    >>> UniversalSet()
    UniversalSet

    >>> Interval(1, 2).intersect(UniversalSet())
    Interval(1, 2)

    See Also
    ========

    EmptySet

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Universal_set
    """

    # in kwargs, etype must be specified in order to determine the universalSet's type, so it is with EmptySet!
    # to instantiate a UniversalSet, use UniversalSet(etype=dtype.integer.set)
    def __new__(cls, **kwargs):
        etype = kwargs.get('etype')
        if etype is not None:
            return etype.universalSet
        return Set.__new__(cls, **kwargs)
        
    def intersection_sets(self, b):
        return b

    def union_sets(self, b):
        return self

    def _complement(self, other):
        return other.etype.emptySet

    def _symmetric_difference(self, other):
        return other

    @property
    def _measure(self):
        return S.Infinity

    def _contains(self, other):
        return S.true

    def as_relational(self, symbol):
        return S.true

    @property
    def _boundary(self):
        return self.etype.emptySet
    
    def _eval_Card(self):
        # Aleph'\N{HEBREW LETTER ALEF}'
        from sympy.core.numbers import Aleph
        if self.etype.is_set:
            print('unknown aleph number??')
            return S.Infinity
        
        if self.etype.is_extended_rational:
            return Aleph(0)
        
        if self.etype.is_hyper_complex:
            return Aleph(1)
        
        print('unknown aleph number??')
        return S.Infinity

    @property
    def etype(self):
        return self._assumptions['etype']

    def __add__(self, other):
        if self.etype.is_set: 
            raise Exception("could not add %s, %s with etype = %s" % (self, other, self.etype))
    
        return self
    
    def __mul__(self, other):
        if self.etype.is_set: 
            raise Exception("could not add %s, %s with etype = %s" % (self, other, self.etype))
        
        return self
    
    def _sympystr(self, _):
        return f'dtype.{self.etype}.universalSet'

    def _lean(self, _):
        return f'dtype.{self.etype}.universalSet'

    def _latex(self, p):
        return r"\mathbb{U}"

    
HyperReals = UniversalSet(etype=dtype.hyper_real)
SuperReals = UniversalSet(etype=dtype.super_real)
HyperComplexes = UniversalSet(etype=dtype.hyper_complex)
SuperComplexes = UniversalSet(etype=dtype.super_complex)

    
class FiniteSet(Set):
    """
    Represents a finite set of discrete numbers

    Examples
    ========

    >>> from sympy import FiniteSet
    >>> FiniteSet(1, 2, 3, 4)
    FiniteSet(1, 2, 3, 4)
    >>> 3 in FiniteSet(1, 2, 3, 4)
    True

    >>> members = [1, 2, 3, 4]
    >>> f = FiniteSet(*members)
    >>> f
    FiniteSet(1, 2, 3, 4)
    >>> f - FiniteSet(2)
    FiniteSet(1, 3, 4)
    >>> f + FiniteSet(2, 5)
    FiniteSet(1, 2, 3, 4, 5)

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Finite_set
    """
    is_iterable = True

    def intersection_sets(self, b):
        if b.is_FiniteSet:
            return FiniteSet(*(self._elements & b._elements))

        try:
            return FiniteSet(*[el for el in self if el in b])
        except TypeError:
            return None  # could not evaluate `el in b` due to symbolic ranges.

    def union_sets(self, b):
        if b.is_FiniteSet:
            return FiniteSet(*(set(self.args) | set(b.args)))
        # If `b` set contains one of my elements, remove it from `a`
        if any(b.contains(x) == True for x in self):
            return set((FiniteSet(*[x for x in self if not b.contains(x)]), b))
        
        if b.is_Intersection:
            for i, s in enumerate(b.args):
                if s.is_FiniteSet:
                    u = [*b.args]
                    del u[i]
                    u = b.func(*u, evaluate=False)
                    if self in u:
                        return b.func((self | s), u, evaluate=False)
        if b.is_Complement:
            A, B = b.args
            if B in self:
                return A | self
#         return None

    def __new__(cls, *args, **kwargs):
        evaluate = kwargs.get('evaluate', global_parameters.evaluate)
        if evaluate:
            args = list(map(sympify, args))

            if len(args) == 0:
                return EmptySet()
        else:
            args = list(map(sympify, args))

        args = list(ordered(set(args), Set._infimum_key))
        obj = Basic.__new__(cls, *args)
        return obj

    def _eval_Eq(self, other):
        if not isinstance(other, FiniteSet):
            if other.is_EmptySet:
                return S.false
            
            if other.is_Interval:
                if not other.etype.is_integer:
                    return S.false
                
            if other.is_set:
                return None
            return S.false

        if len(self) != len(other):
            return S.false

    def __iter__(self):
        return iter(self.args)

    def _complement(self, other):
        from sympy import Range
        if other.is_Range:
            nums = sorted(m for m in self.args if m.is_number)            
            if False and nums != []:
                syms = [m for m in self.args if m.is_Symbol]
                # Reals cannot contain elements other than numbers and symbols.

                intervals = []  # Build up a list of intervals between the elements
                intervals += [Range(S.NegativeInfinity, nums[0])]
                for a, b in zip(nums[:-1], nums[1:]):
                    intervals.append(Range(a + 1, b))  # both open
                intervals.append(Range(nums[-1] + 1, S.Infinity))

                if syms != []:
                    return Complement(Union(*intervals, evaluate=False), FiniteSet(*syms), evaluate=False)
                else:
                    return Union(*intervals, evaluate=False)
            else:

                for i, e in enumerate(self.args):
                    m, M = other.min(), other.max()
                    if e == M:
                        args = [*self.args]
                        del args[i]
                        return other.copy(stop=M, right_open=True) - self.func(*args)
                    if e == m:
                        args = [*self.args]
                        del args[i]
                        return other.copy(start=m, left_open=True).simplify() - self.func(*args)
                    if e > M or e < m:
                        args = [*self.args]
                        del args[i]
                        return other - self.func(*args)
                return
            
            if other.etype.is_integer:
                if other.min() in self: 
                    return other.copy(start=other.start + 1) - self.func(*{*self.args} - {other.min()})                
                if other.max() in self: 
                    return other.copy(stop=other.stop - 1) - self.func(*{*self.args} - {other.max()})
        elif other.is_Interval:
            nums = sorted(m for m in self.args if m.is_number)
            if other.start.is_NegativeInfinity and other.stop.is_Infinity and nums != []:
                left_open = other.left_open
                right_open = other.right_open
                syms = [m for m in self.args if m.is_Symbol]
                # Reals cannot contain elements other than numbers and symbols.

                intervals = []  # Build up a list of intervals between the elements
                intervals += [Interval(S.NegativeInfinity, nums[0], left_open=left_open, right_open=True)]
                for a, b in zip(nums[:-1], nums[1:]):
                    intervals.append(Interval(a, b, left_open=True, right_open=True))  # both open
                intervals.append(Interval(nums[-1], S.Infinity, left_open=True, right_open=right_open))

                if syms != []:
                    return Complement(Union(*intervals, evaluate=False),
                            FiniteSet(*syms), evaluate=False)
                else:
                    return Union(*intervals, evaluate=False)
            else:

                for i, e in enumerate(self.args):
                    m, M = other.min(), other.max()
                    if e == M:
                        args = [*self.args]
                        del args[i]
                        return other.copy(stop=M, right_open=True) - self.func(*args)
                    if e == m:
                        args = [*self.args]
                        del args[i]
                        return other.copy(start=m, left_open=True).simplify() - self.func(*args)
                    if e > M or e < m:
                        args = [*self.args]
                        del args[i]
                        return other - self.func(*args)
                return
            
            if other.etype.is_integer:
                if other.min() in self: 
                    return other.copy(start=other.start + 1) - self.func(*{*self.args} - {other.min()})                
                if other.max() in self: 
                    return other.copy(stop=other.stop - 1) - self.func(*{*self.args} - {other.max()})
            
        elif isinstance(other, FiniteSet):
            s = set(self.args)
            _s = set(other.args)
            
            assert s and _s
            intersection = s & _s
#             s -= intersection
            _s -= intersection
            
            unk = []
            
            for i in s:
                if not all(Equal(e, i).is_BooleanFalse for e in _s):
                    unk.append(i)
                    
            if len(unk) == len(s) and not intersection:
                return
                
            return Complement(FiniteSet(*_s), FiniteSet(*unk))

        return Set._complement(self, other)

    def _contains(self, other):
        """
        Tests whether an element, other, is in the set.

        Relies on Python's set class. This tests for object equality
        All inputs are sympified

        Examples
        ========

        >>> from sympy import FiniteSet
        >>> 1 in FiniteSet(1, 2)
        True
        >>> 5 in FiniteSet(1, 2)
        False

        """
#         r = S.false
        args = []
        for e in self.args:
            # override global evaluation so we can use Eq to do
            # do the evaluation
            t = Eq(e, other, evaluate=True)
            if t is S.true:
                return t
            elif t is not S.false:
                args.append(t)
#                 r = None
        return Or(*args)
#         return r

    @property
    def _boundary(self):
        return self

    @property
    def _inf(self):
        from sympy.functions.elementary.miscellaneous import Min
        return Min(*self)

    @property
    def _sup(self):
        from sympy.functions.elementary.miscellaneous import Max
        return Max(*self)

    @property
    def measure(self):
        return 0

    def __len__(self):
        return len(self.args)

    def as_relational(self, symbol):
        """Rewrite a FiniteSet in terms of equalities and logic operators. """
        from sympy.core.relational import Eq
        return Or(*[Eq(symbol, elem) for elem in self])

    def compare(self, other):
        return (hash(self) - hash(other))

    def _eval_evalf(self, prec):
        return FiniteSet(*[elem._eval_evalf(prec) for elem in self])

    @property
    def _sorted_args(self):
        return self.args

    def _eval_powerset(self):
        return self.func(*[self.func(*s) for s in subsets(self.args)])

    def __ge__(self, other):
        if not other.is_set:
            raise TypeError("Invalid comparison of set with %s" % func_name(other))
        return other.is_subset(self)

    def __gt__(self, other):
        if not other.is_set:
            raise TypeError("Invalid comparison of set with %s" % func_name(other))
        return self.is_proper_superset(other)

    def __le__(self, other):
        if not other.is_set:
            raise TypeError("Invalid comparison of set with %s" % func_name(other))
        return self.is_subset(other)

    def __lt__(self, other):
        if not other.is_set:
            raise TypeError("Invalid comparison of set with %s" % func_name(other))
        return self.is_proper_subset(other)

    def _eval_Card(self):
        length = len(self)
        if length == 1:
            return S.One
        from sympy.functions.elementary.piecewise import Piecewise
        * before, last = self.args
        from sympy import Card
        before = self.func(*before)
        length = Card(before)
        return Piecewise((length, Element(last, before).simplify()), (length + 1, True)).simplify()

    def _eval_is_finiteset(self):
        return True

    def _eval_is_extended_integer(self):
        return fuzzy_et(e.is_extended_integer for e in self.args)
    
    def _eval_is_super_integer(self):
        return fuzzy_et(e.is_super_integer for e in self.args)
    
    def _eval_is_extended_rational(self):
        return fuzzy_et(e.is_extended_rational for e in self.args)
    
    def _eval_is_super_rational(self):
        return fuzzy_et(e.is_super_rational for e in self.args)

    def _eval_is_hyper_rational(self):
        return fuzzy_et(e.is_hyper_rational for e in self.args)
    
    def _eval_is_extended_real(self):
        return fuzzy_et(e.is_extended_real for e in self.args) 

    def _eval_is_hyper_real(self):
        return fuzzy_et(e.is_hyper_real for e in self.args)
    
    def _eval_is_super_real(self):
        return fuzzy_et(e.is_super_real for e in self.args)
    
    def _eval_is_extended_complex(self):
        return fuzzy_et(e.is_extended_complex for e in self.args)
     
    def _eval_is_hyper_complex(self):
        return fuzzy_et(e.is_hyper_complex for e in self.args)
    
    @property
    def etype(self):
        dtype = None
        for e in self:
            _dtype = e.type
            if dtype is None:
                dtype = _dtype
                continue
            if dtype != _dtype:
                if dtype in _dtype:
                    dtype = _dtype
                elif _dtype in dtype:
                    ...
                else:
                    raise Exception('inconsistent dtype detected: %s != %s' % (dtype, _dtype))
        return dtype

    def min(self):
        from sympy.functions.elementary.miscellaneous import Min
        return Min(*self.args)        

    def max(self):
        from sympy.functions.elementary.miscellaneous import Max
        return Max(*self.args)        

    def __add__(self, other):
        if other.is_set:
            return Union(*(other + arg for arg in self.args))
        return self.func(*(arg + other for arg in self.args))

    def __neg__(self):
        return self.func(*(-arg for arg in self.args))
    
    def handle_finite_sets(self, unk):
        if len(unk) == len(self) == 1:
            return Intersection(unk, self, evaluate=False)

    @cacheit
    def _eval_domain_defined(self, x, **_):
        domain = Set._eval_domain_defined(self, x)        
        for arg in self.args:
            domain &= arg.domain_defined(x)        
        return domain

    def sum(self):
        # return the sum of elements in the finiteset
        length = len(self)
        if length == 1:
            return self.arg
        from sympy.functions.elementary.piecewise import Piecewise
        * before, last = self.args
        before = self.func(*before)
        sum_of_before = before.sum()
        return Piecewise((sum_of_before, Element(last, before).simplify()), (sum_of_before + last, True)).simplify()

    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a FiniteSet object!
        """
        if rhs.is_FiniteSet:
            if len(lhs) == len(rhs) == 1:
                return self.func(lhs.arg, rhs.arg)
        
    @classmethod
    def simplify_Element(cls, self, e, s):
        """
        precondition: self.lhs is a FiniteSet object!
        """
        if len(s) == 1:
            y, *_ = s
            if not e._has(Symbol) and y._has(Symbol):
                return Equal(y, e)
            return Equal(e, y)

    @classmethod
    def simplify_NotElement(cls, self, e, s):
        """
        precondition: self.lhs is a FiniteSet object!
        """
        from sympy import Unequal
        if len(s) == 1:
            y, *_ = s
            return Unequal(e, y)
        return And(*(Unequal(e, y) for y in s))

    def _eval_Subset_reversed(self, lhs):
        if lhs.is_UniversalSet:
            return S.false
    
    def _sympystr(self, p):
        from sympy import default_sort_key
        printset = sorted(self, key=default_sort_key)
        args = [p._print(el) for el in printset]
        for i in range(len(printset)):
            if printset[i].is_FiniteSet:
                args[i] = 'FiniteSet(%s)' % args[i][1:-1]

        return '{%s}' % ', '.join(args)

    def _lean(self, p):
        from sympy import default_sort_key
        printset = sorted(self, key=default_sort_key)
        args = [p._print(el) for el in printset]
        for i in range(len(printset)):
            if printset[i].is_FiniteSet:
                args[i] = '{%s}' % args[i][1:-1]

        return '{%s}' % ', '.join(args)

    def _latex(self, p):
        from sympy import default_sort_key
        return p._print_set(sorted(self.args, key=default_sort_key))


from sympy.core.sympify import converter
converter[set] = lambda x: FiniteSet(*x)
converter[frozenset] = lambda x: FiniteSet(*x)


class SymmetricDifference(Set):
    """Represents the set of elements which are in either of the
    sets and not in their intersection.

    Examples
    ========

    >>> from sympy import SymmetricDifference, FiniteSet
    >>> SymmetricDifference(FiniteSet(1, 2, 3), FiniteSet(3, 4, 5))
    FiniteSet(1, 2, 4, 5)

    See Also
    ========

    Complement, Union

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Symmetric_difference
    """

    is_SymmetricDifference = True

    def __new__(cls, a, b, evaluate=True):
        if evaluate:
            return SymmetricDifference.reduce(a, b)

        return Basic.__new__(cls, a, b)

    @staticmethod
    def reduce(A, B):
        result = B._symmetric_difference(A)
        if result is not None:
            return result
        else:
            return SymmetricDifference(A, B, evaluate=False)


def imageset(sym, expr, baseset):
    from sympy.concrete.sets import Cup
    if baseset.is_Range:
        limit = (sym, baseset.min(), baseset.max() + 1)
    elif baseset.is_Element and baseset.lhs == sym:
        limit = (sym, baseset.rhs)
    else:
        limit = (sym, baseset)
    return Cup({expr}, limit)


# by definition, we have
# ConditionSet(variable, condition, base_set) == Union[variable:condition:base_set]({variable})
def conditionset(*limit):
    from sympy.concrete.sets import Cup
    if len(limit) > 2 and (limit[2] is None or limit[2].is_UniversalSet):
        limit = limit[:2]
    variable, condition, *base_set = limit
    if base_set:
        base_set = base_set[0]
        if not base_set:
            return base_set
    else:
        base_set = variable.universalSet
       
    if condition:
        return base_set
    if condition.is_BooleanFalse:
        return variable.emptySet

    return Cup({variable}, limit)


def _imageset(*args):
    r"""
    Return an image of the set under transformation ``f``.

    If this function can't compute the image, it returns an
    unevaluated ImageSet object.

    .. math::
        { f(x) | x \in self }

    Examples
    ========

    >>> from sympy import S, Interval, Symbol, imageset, sin, Lambda
    >>> from sympy.abc import x, y

    >>> imageset(x, 2*x, Interval(0, 2))
    Interval(0, 4)

    >>> imageset(lambda x: 2*x, Interval(0, 2))
    Interval(0, 4)

    >>> imageset(Lambda(x, sin(x)), Interval(-2, 1))
    ImageSet(Lambda(x, sin(x)), Interval(-2, 1))

    >>> imageset(sin, Interval(-2, 1))
    ImageSet(Lambda(x, sin(x)), Interval(-2, 1))
    >>> imageset(lambda y: x + y, Interval(-2, 1))
    ImageSet(Lambda(y, x + y), Interval(-2, 1))

    Expressions applied to the set of Integers are simplified
    to show as few negatives as possible and linear expressions
    are converted to a canonical form. If this is not desirable
    then the unevaluated ImageSet should be used.

    >>> imageset(x, -2*x + 5, S.Integers)
    ImageSet(Lambda(x, 2*x + 1), Integers)

    See Also
    ========

    sympy.sets.fancysets.ImageSet

    """
    from sympy.core import Lambda
    from sympy.sets.fancysets import ImageSet
    from sympy.sets.setexpr import set_function

    if len(args) < 2:
        raise ValueError('imageset expects at least 2 args, got: %s' % len(args))

    from sympy.tensor.indexed import Sliced
    if isinstance(args[0], (Symbol, tuple, Sliced)) and len(args) > 2:
        f = Lambda(args[0], args[1])
        set_list = args[2:]
    else:
        f = args[0]
        set_list = args[1:]

    if isinstance(f, Lambda):
        pass
    elif callable(f):
        nargs = getattr(f, 'nargs', {})
        if nargs:
            if len(nargs) != 1:
                raise NotImplemented(filldedent('''
                    This function can take more than 1 arg
                    but the potentially complicated set input
                    has not been analyzed at this point to
                    know its dimensions. TODO
                    '''))
            N = nargs.args[0]
            if N == 1:
                s = 'x'
            else:
                s = [Symbol('x%i' % i) for i in range(1, N + 1)]
        else:
            s = inspect.signature(f).parameters

        dexpr = _sympify(f(*[Dummy() for i in s]))
        var = [_uniquely_named_symbol(Symbol(i), dexpr) for i in s]
        expr = f(*var)
        f = Lambda(var, expr)
    else:
        raise TypeError(filldedent('''
            expecting lambda, Lambda
            not \'%s\'.''' % func_name(f)))

    if any(not s.is_set for s in set_list):
        name = [func_name(s) for s in set_list]
        raise ValueError('arguments after mapping should be sets, not %s' % name)

    if len(set_list) == 1:
        set = set_list[0]
        try:
            # TypeError if arg count != set dimensions
            r = set_function(f, set)
            if r is None:
                raise TypeError
            if not r:
                return r
        except TypeError:
            r = ImageSet(f, set)
        if isinstance(r, ImageSet):
            f, set = r.args

        if f.variables == f.expr:
            return set

        if isinstance(set, ImageSet):
            if len(set.lamda.variables) == 1 and len(f.variables) == 1:
                return imageset(Lambda(set.lamda.variables[0],
                                       f.expr.subs(f.variables[0], set.lamda.expr)),
                                set.base_set)

        if r is not None:
            return r

    return ImageSet(f, *set_list)


def is_function_invertible_in_set(func, setv):
    """
    Checks whether function ``func`` is invertible when the domain is
    restricted to set ``setv``.
    """
    from sympy import exp, log
    # Functions known to always be invertible:
    if func in (exp, log):
        return True
    u = Dummy("u")
    fdiff = func(u).diff(u)
    # monotonous functions:
    # TODO: check subsets (`func` in `setv`)
    if (fdiff > 0) == True or (fdiff < 0) == True:
        return True
    # TODO: support more
    return None


def simplify_union(args):
    """
    Simplify a :class:`Union` using known rules

    We first start with global rules like 'Merge all FiniteSets'

    Then we iterate through all pairs and ask the constituent sets if they
    can simplify themselves with any other constituent.  This process depends
    on ``union_sets(a, b)`` functions.
    """
#     from sympy.sets.handlers.union import union_sets

    # ===== Global Rules =====
    if not args:
        return EmptySet()

    for arg in args:
        if not arg.is_set:
            raise TypeError("Input args to Union must be Sets")

    # Merge all finite sets
    finite_sets = [x for x in args if x.is_FiniteSet]
    if len(finite_sets) > 1:
        args = [x for x in args if not x.is_FiniteSet]        
        a = [x for s in finite_sets for x in s]
        if a:
            from sympy import FiniteSet
            args.append(FiniteSet(*a))
        elif not args:
            args = finite_sets[:1]            

    # ===== Pair-wise Rules =====
    # Here we depend on rules built into the constituent sets
    args = set(args)
    new_args = True
    while new_args:
        for s in args:
            new_args = False
            for t in args - set((s,)):
                new_set = s.union_sets(t)
                # This returns None if s does not know how to intersect
                # with t. Returns the newly intersected set otherwise
                if new_set is not None:
                    if not isinstance(new_set, set):
                        new_set = set((new_set,))
                    new_args = (args - set((s, t))).union(new_set)
                    break
            if new_args:
                args = new_args
                break

    if len(args) == 1:
        return args.pop()
    else:
        return Union(*args, evaluate=False)


def simplify_intersection(args):
    """
    Simplify an intersection using known rules

    We first start with global rules like
    'if any empty sets return empty set' and 'distribute any unions'

    Then we iterate through all pairs and ask the constituent sets if they
    can simplify themselves with any other constituent
    """

    # ===== Global Rules =====
    if not args:
        print('warning: UniversalSet without etype is prohibited!')
        return UniversalSet()
    # If any EmptySets return EmptySet
    for s in args:
        if not s.is_set:
            raise TypeError("Input args to Union must be Sets")
        
        if s.is_EmptySet:
            return s
    # Handle Finite sets
    rv = Intersection._handle_finite_sets(args)

    if rv is not None:
        return rv

    # If any of the sets are unions, return a Union of Intersections
    for s in args:
        if s.is_Union:
            other_sets = set(args) - set((s,))
            if len(other_sets) > 0:
                other = Intersection(*other_sets)
                return Union(*(Intersection(arg, other) for arg in s.args))
            else:
                return Union(*[arg for arg in s.args])

    for s in args:
        if s.is_Complement:
            args.remove(s)
            other_sets = args + [s.args[0]]
            return Complement(Intersection(*other_sets), s.args[1])

    # At this stage we are guaranteed not to have any
    # EmptySets, FiniteSets, or Unions in the intersection

    # ===== Pair-wise Rules =====
    # Here we depend on rules built into the constituent sets
    args = set(args)
    new_args = True
    while new_args:
        for s in args:
            new_args = False
            for t in args - set((s,)):
                new_set = s.intersection_sets(t)
                # This returns None if s does not know how to intersect
                # with t. Returns the newly intersected set otherwise

                if new_set is not None:
                    new_args = (args - set((s, t))).union(set((new_set,)))
                    break
            if new_args:
                args = new_args
                break

    if len(args) == 1:
        return args.pop()
    else:
        return Intersection(*args, evaluate=False)


def _handle_finite_sets(op, x, y, commutative):
    # Handle finite sets:
    from sympy import FiniteSet
    fs_args, other = sift([x, y], lambda x: isinstance(x, FiniteSet), binary=True)
    if len(fs_args) == 2:
        return FiniteSet(*[op(i, j) for i in fs_args[0] for j in fs_args[1]])
    elif len(fs_args) == 1:
        sets = [_apply_operation(op, other[0], i, commutative) for i in fs_args[0]]
        return Union(*sets)
    else:
        return None


def _apply_operation(op, x, y, commutative):
    from sympy.sets import ImageSet
    from sympy import symbols, Lambda
    d = Dummy('d')

    out = _handle_finite_sets(op, x, y, commutative)
    if out is None:
        out = op(x, y)

    if out is None and commutative:
        out = op(y, x)
    if out is None:
        _x, _y = symbols("x y")
        if x.is_set and not y.is_set:
            out = ImageSet(Lambda(d, op(d, y)), x).doit()
        elif not x.is_set and y.is_set:
            out = ImageSet(Lambda(d, op(x, d)), y).doit()
        else:
            out = ImageSet(Lambda((_x, _y), op(_x, _y)), x, y)
    return out


def set_add(x, y):
    from sympy.sets.handlers.add import _set_add
    return _apply_operation(_set_add, x, y, commutative=True)


def set_sub(x, y):
    from sympy.sets.handlers.add import _set_sub
    return _apply_operation(_set_sub, x, y, commutative=False)


def set_mul(x, y):
    from sympy.sets.handlers.mul import _set_mul
    return _apply_operation(_set_mul, x, y, commutative=True)


def set_div(x, y):
    from sympy.sets.handlers.mul import _set_div
    return _apply_operation(_set_div, x, y, commutative=False)


def set_pow(x, y):
    from sympy.sets.handlers.power import _set_pow
    return _apply_operation(_set_pow, x, y, commutative=False)


def set_function(f, x):
    from sympy.sets.handlers.functions import _set_function
    return _set_function(f, x)
