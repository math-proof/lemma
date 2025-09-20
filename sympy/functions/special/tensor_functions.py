from sympy.core import S, Integer
from sympy.core.compatibility import SYMPY_INTS
from sympy.core.function import Function
from sympy.core.logic import fuzzy_not
from sympy.core.mul import prod
from sympy.utilities.iterables import (has_dups, default_sort_key)

###############################################################################
###################### Kronecker Delta, Levi-Civita etc. ######################
###############################################################################


def Eijk(*args, **kwargs):
    """
    Represent the Levi-Civita symbol.

    This is just compatibility wrapper to ``LeviCivita()``.

    See Also
    ========

    LeviCivita

    """
    return LeviCivita(*args, **kwargs)


def eval_levicivita(*args):
    """Evaluate Levi-Civita symbol."""
    from sympy import factorial
    n = len(args)
    return prod(
        prod(args[j] - args[i] for j in range(i + 1, n))
        / factorial(i) for i in range(n))
    # converting factorial(i) to int is slightly faster


class LeviCivita(Function):
    """Represent the Levi-Civita symbol.

    For even permutations of indices it returns 1, for odd permutations -1, and
    for everything else (a repeated index) it returns 0.

    Thus it represents an alternating pseudotensor.

    Examples
    ========

    >>> from sympy import LeviCivita
    >>> from sympy.abc import i, j, k
    >>> LeviCivita(1, 2, 3)
    1
    >>> LeviCivita(1, 3, 2)
    -1
    >>> LeviCivita(1, 2, 2)
    0
    >>> LeviCivita(i, j, k)
    LeviCivita(i, j, k)
    >>> LeviCivita(i, j, i)
    0

    See Also
    ========

    Eijk

    """

    is_integer = True

    @classmethod
    def eval(cls, *args):
        if all(isinstance(a, (SYMPY_INTS, Integer)) for a in args):
            return eval_levicivita(*args)
        if has_dups(args):
            return S.Zero

    def doit(self):
        return eval_levicivita(*self.args)


class KroneckerDelta(Function):
    """The discrete, or Kronecker, delta function.

    A function that takes in two integers `i` and `j`. It returns `0` if `i` and `j` are
    not equal or it returns `1` if `i` and `j` are equal.

    Parameters
    ==========

    i : Number, Symbol
        The first index of the delta function.
    j : Number, Symbol
        The second index of the delta function.

    Examples
    ========

    A simple example with integer indices::

        >>> from sympy.functions.special.tensor_functions import KroneckerDelta
        >>> KroneckerDelta(1, 2)
        0
        >>> KroneckerDelta(3, 3)
        1

    Symbolic indices::

        >>> from sympy.abc import i, j, k
        >>> KroneckerDelta(i, j)
        KroneckerDelta(i, j)
        >>> KroneckerDelta(i, i)
        1
        >>> KroneckerDelta(i, i + 1)
        0
        >>> KroneckerDelta(i, i + 1 + k)
        KroneckerDelta(i, i + k + 1)

    See Also
    ========

    eval
    sympy.functions.special.delta_functions.DiracDelta

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Kronecker_delta
    https://encyclopediaofmath.org/wiki/Legendre%E2%80%93Jacobi%E2%80%93Kronecker_symbol
    """
    is_extended_nonnegative = True
    is_integer = True

    @classmethod
    def eval(cls, i, j):
        """
        Evaluates the discrete delta function.

        Examples
        ========

        >>> from sympy.functions.special.tensor_functions import KroneckerDelta
        >>> from sympy.abc import i, j, k

        >>> KroneckerDelta(i, j)
        KroneckerDelta(i, j)
        >>> KroneckerDelta(i, i)
        1
        >>> KroneckerDelta(i, i + 1)
        0
        >>> KroneckerDelta(i, i + 1 + k)
        KroneckerDelta(i, i + k + 1)

        # indirect doctest

        """
        if i.is_set:
            from sympy import Equal
            delta = Equal(i, j)
            if delta == True:
                return S.One
            if delta == False:
                return S.Zero
        else:
            diff = i - j
            if diff.is_zero:
                return S.One
            if fuzzy_not(diff.is_zero):
                return S.Zero
            if diff.is_nonzero:
                return S.Zero
            from sympy import Element
            if Element(i, j.domain).is_BooleanFalse or Element(j, i.domain).is_BooleanFalse:
                return S.Zero
            
            if i.assumptions0.get("below_fermi") and j.assumptions0.get("above_fermi"):
                return S.Zero
            if j.assumptions0.get("below_fermi") and i.assumptions0.get("above_fermi"):
                return S.Zero
            
            if i.is_Add and j.is_Add:
                i_args = set(i.args)
                j_args = set(j.args)
                intersect = i_args & j_args
                if intersect:
                    i_args -= intersect
                    j_args -= intersect
                    i = i.func(*i_args)
                    j = j.func(*j_args)                        
                    return cls(i, j)
                
            if j.is_KroneckerDelta:
                if i == 1:
                    return j
                if i == 0:
                    return 1 - j
        # to make KroneckerDelta canonical
        # following lines will check if inputs are in order
        # if not, will return KroneckerDelta with correct order
        if i is not min(i, j, key=default_sort_key):
            return cls(j, i)

    def _eval_power(self, expt):
        if expt.is_positive:
            return self
        if expt.is_negative and not -expt is S.One:
            return 1 / self

    @property
    def is_above_fermi(self):
        """
        True if Delta can be non-zero above fermi

        Examples
        ========

        >>> from sympy.functions.special.tensor_functions import KroneckerDelta
        >>> from sympy import Symbol
        >>> a = Symbol('a', above_fermi=True)
        >>> i = Symbol('i', below_fermi=True)
        >>> p = Symbol('p')
        >>> q = Symbol('q')
        >>> KroneckerDelta(p, a).is_above_fermi
        True
        >>> KroneckerDelta(p, i).is_above_fermi
        False
        >>> KroneckerDelta(p, q).is_above_fermi
        True

        See Also
        ========

        is_below_fermi, is_only_below_fermi, is_only_above_fermi


        """
        if self.args[0].assumptions0.get("below_fermi"):
            return False
        if self.args[1].assumptions0.get("below_fermi"):
            return False
        return True

    @property
    def is_below_fermi(self):
        """
        True if Delta can be non-zero below fermi

        Examples
        ========

        >>> from sympy.functions.special.tensor_functions import KroneckerDelta
        >>> from sympy import Symbol
        >>> a = Symbol('a', above_fermi=True)
        >>> i = Symbol('i', below_fermi=True)
        >>> p = Symbol('p')
        >>> q = Symbol('q')
        >>> KroneckerDelta(p, a).is_below_fermi
        False
        >>> KroneckerDelta(p, i).is_below_fermi
        True
        >>> KroneckerDelta(p, q).is_below_fermi
        True

        See Also
        ========

        is_above_fermi, is_only_above_fermi, is_only_below_fermi

        """
        if self.args[0].assumptions0.get("above_fermi"):
            return False
        if self.args[1].assumptions0.get("above_fermi"):
            return False
        return True

    @property
    def is_only_above_fermi(self):
        """
        True if Delta is restricted to above fermi

        Examples
        ========

        >>> from sympy.functions.special.tensor_functions import KroneckerDelta
        >>> from sympy import Symbol
        >>> a = Symbol('a', above_fermi=True)
        >>> i = Symbol('i', below_fermi=True)
        >>> p = Symbol('p')
        >>> q = Symbol('q')
        >>> KroneckerDelta(p, a).is_only_above_fermi
        True
        >>> KroneckerDelta(p, q).is_only_above_fermi
        False
        >>> KroneckerDelta(p, i).is_only_above_fermi
        False

        See Also
        ========

        is_above_fermi, is_below_fermi, is_only_below_fermi


        """
        return (self.args[0].assumptions0.get("above_fermi")
                or
                self.args[1].assumptions0.get("above_fermi")
                ) or False

    @property
    def is_only_below_fermi(self):
        """
        True if Delta is restricted to below fermi

        Examples
        ========

        >>> from sympy.functions.special.tensor_functions import KroneckerDelta
        >>> from sympy import Symbol
        >>> a = Symbol('a', above_fermi=True)
        >>> i = Symbol('i', below_fermi=True)
        >>> p = Symbol('p')
        >>> q = Symbol('q')
        >>> KroneckerDelta(p, i).is_only_below_fermi
        True
        >>> KroneckerDelta(p, q).is_only_below_fermi
        False
        >>> KroneckerDelta(p, a).is_only_below_fermi
        False

        See Also
        ========

        is_above_fermi, is_below_fermi, is_only_above_fermi


        """
        return (self.args[0].assumptions0.get("below_fermi")
                or
                self.args[1].assumptions0.get("below_fermi")
                ) or False

    @property
    def indices_contain_equal_information(self):
        """
        Returns True if indices are either both above or below fermi.

        Examples
        ========

        >>> from sympy.functions.special.tensor_functions import KroneckerDelta
        >>> from sympy import Symbol
        >>> a = Symbol('a', above_fermi=True)
        >>> i = Symbol('i', below_fermi=True)
        >>> p = Symbol('p')
        >>> q = Symbol('q')
        >>> KroneckerDelta(p, q).indices_contain_equal_information
        True
        >>> KroneckerDelta(p, q+1).indices_contain_equal_information
        True
        >>> KroneckerDelta(i, p).indices_contain_equal_information
        False

        """
        if (self.args[0].assumptions0.get("below_fermi") and
                self.args[1].assumptions0.get("below_fermi")):
            return True
        if (self.args[0].assumptions0.get("above_fermi")
                and self.args[1].assumptions0.get("above_fermi")):
            return True

        # if both indices are general we are True, else false
        return self.is_below_fermi and self.is_above_fermi

    @property
    def preferred_index(self):
        """
        Returns the index which is preferred to keep in the final expression.

        The preferred index is the index with more information regarding fermi
        level.  If indices contain same information, 'a' is preferred before
        'b'.

        Examples
        ========

        >>> from sympy.functions.special.tensor_functions import KroneckerDelta
        >>> from sympy import Symbol
        >>> a = Symbol('a', above_fermi=True)
        >>> i = Symbol('i', below_fermi=True)
        >>> j = Symbol('j', below_fermi=True)
        >>> p = Symbol('p')
        >>> KroneckerDelta(p, i).preferred_index
        i
        >>> KroneckerDelta(p, a).preferred_index
        a
        >>> KroneckerDelta(i, j).preferred_index
        i

        See Also
        ========

        killable_index

        """
        if self._get_preferred_index():
            return self.args[1]
        else:
            return self.args[0]

    @property
    def killable_index(self):
        """
        Returns the index which is preferred to substitute in the final
        expression.

        The index to substitute is the index with less information regarding
        fermi level.  If indices contain same information, 'a' is preferred
        before 'b'.

        Examples
        ========

        >>> from sympy.functions.special.tensor_functions import KroneckerDelta
        >>> from sympy import Symbol
        >>> a = Symbol('a', above_fermi=True)
        >>> i = Symbol('i', below_fermi=True)
        >>> j = Symbol('j', below_fermi=True)
        >>> p = Symbol('p')
        >>> KroneckerDelta(p, i).killable_index
        p
        >>> KroneckerDelta(p, a).killable_index
        p
        >>> KroneckerDelta(i, j).killable_index
        j

        See Also
        ========

        preferred_index

        """
        if self._get_preferred_index():
            return self.args[0]
        else:
            return self.args[1]

    def _get_preferred_index(self):
        """
        Returns the index which is preferred to keep in the final expression.

        The preferred index is the index with more information regarding fermi
        level.  If indices contain same information, index 0 is returned.
        """
        if not self.is_above_fermi:
            if self.args[0].assumptions0.get("below_fermi"):
                return 0
            else:
                return 1
        elif not self.is_below_fermi:
            if self.args[0].assumptions0.get("above_fermi"):
                return 0
            else:
                return 1
        else:
            return 0

    @property
    def indices(self):
        return self.args[0:2]

    def domain_nonzero(self, x):
        from sympy import Equal
        domain = x.domain_conditioned(Equal(*self.args, evaluate=False))
        if domain.is_ConditionSet:
            return x.domain
        return domain

    def _eval_shape(self):
        return ()

    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        return dtype.integer

    def _sympystr(self, p):
        return 'KroneckerDelta(%s)' % ', '.join(p._print(arg) for arg in self.args)
        
    def _lean(self, p):
        return Function.lean_fun('KroneckerDelta', *self.args, p=p)

    def _latex(self, p, exp=None):
        i = p._print(self.args[0])
        j = p._print(self.args[1])
        if self.args[0].is_Atom and self.args[1].is_Atom:
            tex = r'\delta_{%s %s}' % (i, j)
        else:
            tex = r'\delta_{%s, %s}' % (i, j)
        if exp is not None:
            tex = r'\left(%s\right)^{%s}' % (tex, exp)
        return tex
        
    @property
    def domain(self):
        from sympy.sets.sets import FiniteSet
        return FiniteSet(0, 1)

    def enumerate_KroneckerDelta(self):
        yield self
        
    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a KroneckerDelta object!
        """
        if rhs.is_One:        
            return self.func(*lhs.args).simplify()
        return Function.simplify_Equal(self, lhs, rhs)
            
    @classmethod
    def simplify_Unequal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a KroneckerDelta object!
        """
        if rhs.is_zero:
            return self.func.invert_type(*lhs.args)
        elif rhs.is_One:
            return self.func(*lhs.args)


class Bool(Function):
    """IversonBracket function
    https://en.wikipedia.org/wiki/Iverson_bracket
    """

    def __new__(cls, arg):
        obj = Function.__new__(cls, arg)
        if not arg.is_bool:
            if 'super_complex' in obj._assumptions:
                del obj._assumptions['super_complex']
        return obj
    
    @classmethod
    def eval(cls, cond):
        """
        Evaluates IversonBracket function
        """
        if cond.dtype.is_bool:
            if cond == True:
                return S.One
            if cond.is_BooleanFalse:
                return S.Zero
        else:
            if cond.shape:
                if cond.is_DenseMatrix:
                    args = []
                    for arg in cond.args:
                        arg = cls.eval(arg)
                        if arg is None:
                            return
                        args.append(arg)
                    
                    return cond.func(*args, shape=cond.shape)
            else:
                if cond.is_nonzero:
                    return S.true
                if cond.is_zero:
                    return S.false

    def _eval_is_extended_integer(self):
        return self.arg.is_bool

    def _eval_is_extended_rational(self):
        return self.arg.is_bool
    
    def _eval_is_extended_real(self):
        return self.arg.is_bool
        
    def _eval_is_extended_complex(self):
        return self.arg.is_bool
        
    def _eval_is_super_complex(self):
        return self.arg.is_bool
    
    def _eval_is_finite(self):
        return True
        
    def _eval_is_bool(self):
        return not self.arg.is_bool
        
    def _eval_is_extended_nonnegative(self):
        return self.arg.is_bool
        
    def _eval_is_extended_negative(self):
        return not self.arg.is_bool
    
    def domain_nonzero(self, x):
        domain = x.domain_conditioned(self.arg)
        if domain.is_ConditionSet:
            return x.domain
        return domain

    def _eval_shape(self):
        return self.arg.shape

    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        if self.arg.is_bool:
            return dtype.integer
        else:
            return dtype.bool

    def _sympystr(self, p):
        return 'Bool(%s)' % p._print(self.arg)

    def _lean(self, p):
        arg = self.arg
        argStr = p._print(arg)
        if arg.is_Quantifier or arg.is_BinaryCondition:
            argStr = '(%s)' % argStr
        return 'Bool.toNat ' + argStr

    def _latex(self, p, exp=None):
        cond = p._print(self.arg)
        cond = r'\left|%s\right|' % cond
        if exp is not None:
            cond = "{%s}^{%s}" % (cond, p._print(exp))
        return cond
        
    @property
    def domain(self):
        from sympy.sets.sets import FiniteSet
        if self.arg.is_bool:
            return FiniteSet(S.Zero, S.One)
        else:
            shape = self.shape
            domain = FiniteSet(S.false, S.true)
            if shape:
                from sympy.sets.sets import CartesianSpace
                domain = CartesianSpace(domain, *shape)
            return domain

    def inference_status(self, child):
        raise Exception("boolean conditions within Bool are not applicable for inequivalent inference!")
    
    def __iter__(self):
        raise TypeError
        
    def __getitem__(self, indices):
        return self.func(self.arg[indices])
        
    @property
    def domain_assumed(self):
        return self.domain

    def monotonicity(self, x):
        return (S.Zero, S.One), 0
