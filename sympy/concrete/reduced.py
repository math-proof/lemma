from sympy.core.function import Function
from sympy.concrete.summations import Sum
from sympy.core.cache import cacheit
from sympy.core.singleton import S
from sympy.concrete.expr_with_limits import Minima, Maxima
from sympy.core.containers import Tuple


class Reduced(Function):
    is_elementwise = False

    def __new__(cls, *args, **options):
        if len(args) > 1 and isinstance(args[-1], tuple):
            arg, *axis = args
            axis = tuple(axis for axis, in axis)
            if len(axis) == 1:
                axis, = axis
        else:
            arg, = args
            if isinstance(arg, dict):
                arg = S(arg)
            axis = -1
        axis = arg.normalize_reduced_axis(axis)

        if options.get('evaluate', True):
            result = cls.eval(arg, axis=axis)
            if result is not None:
                return result
            
        from sympy.core.basic import Basic
        obj = Basic.__new__(cls, arg)
        obj.axis = Tuple(*axis) if isinstance(axis, tuple) else S(axis)
        return obj

    def _subs(self, old, new, **hints):
        #need to consider the shape reduction, if the shape is reduced, then reduced operator should be removed!
        if old == new:
            return self

        if old.is_Sliced:
            this = self._subs_sliced(old, new, **hints)
            if this != self:
                return this
        
        from sympy.core.basic import _aresame
        if _aresame(self, old) or self.dummy_eq(old):
            return new

        arg = self.arg._subs(old, new, **hints)
        if not _aresame(arg, self.arg):
            if len(arg.shape) < len(self.arg.shape):
                return arg

            return self.func(arg)

        return self

    def _hashable_content(self):
        axis = self.axis
        if not isinstance(axis, (tuple, Tuple)):
            axis = axis,
        return super()._hashable_content() + axis

    @cacheit
    def _eval_shape(self):
        axis = self.axis
        [*shape] = self.arg.shape
        if shape:
            if isinstance(axis, (tuple, Tuple)):
                for axis in reversed(axis):
                    del shape[axis]
            else:
                del shape[axis]
        return tuple(shape)

    @property
    def default_axis(self):
        return len(self.arg.shape) - 1


class ReducedSum(Reduced):
    r"""Represents unevaluated reduced summation.
    input must be a multi-dimensional tensor
    """
    is_complex = True
    
    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.arg.is_zero:
            return True
        
        if self.arg.is_extended_positive or self.arg.is_extended_negative:
            return False

    def doit(self, **hints):
        deep = hints.get('deep', True)
        if deep:
            f = self.arg.doit(**hints)
        else:
            f = self.arg

        if f.is_FiniteSet:
            x, *args = f.args
            rest = f.func(*args)
            from sympy import NotElement, Bool
            sgm = x * Bool(NotElement(x, rest).simplify()).simplify()
            if not rest:
                return sgm
            return self.func(rest).doit(deep=deep) + sgm
        return self

    @property
    def dtype(self):
        return self.arg.dtype

    def _sympystr(self, p):
        axis = self.axis
        if axis == self.default_axis:
            return 'ReducedSum(%s)' % p._print(self.arg)
        else:
            if isinstance(axis, (tuple, Tuple)):
                axis = ', '.join(p._print(axis) for axis in axis)
            else:
                axis = p._print(axis)
            return 'ReducedSum[%s](%s)' % (axis, p._print(self.arg))

    def _lean(self, p):
        # return '\N{N-ARY SUMMATION}(%s)' % p._print(self.arg)
        axis = self.axis
        if axis == self.default_axis:
            return Function.lean_method('sum', self.arg, p=p)
        else:
            if not isinstance(axis, (tuple, Tuple)):
                axis = (axis,)
            return Function.lean_method('sum', self.arg, *axis, p=p)

    def _latex(self, p, exp=None):
        axis = self.axis
        expr = p._print(self.arg)
        if self.arg.is_Add or self.arg.is_MatMul:
            expr = r"\left(%s\right)" % expr

        if axis == self.default_axis:
            expr = r"\sum{%s}" % expr
            if exp is None:
                return expr
        else:
            if isinstance(axis, (tuple, Tuple)):
                axis = ', '.join(p._print(axis) for axis in axis)
            else:
                axis = p._print(axis)
            expr = r"\sum\nolimits_{%s}{%s}" % (axis, expr)
            if exp is None:
                return expr
        return r"\left(%s\right)^{%s}" % (expr, exp)

    
    def _eval_is_finite(self):
        return self.arg.is_finite

    def _eval_is_extended_integer(self):
        return self.arg.is_extended_integer
    
    def _eval_is_extended_real(self):
        return self.arg.is_extended_real

    def _eval_is_extended_positive(self):
        return self.arg.is_extended_positive
    
    def _eval_is_extended_negative(self):
        return self.arg.is_extended_negative

    def _eval_exp(self):
        from sympy import log, Product
        if isinstance(self.arg, log):
            return Product(self.arg.arg, *self.limits)

    def _eval_derivative(self, x):
        from sympy.core.function import Derivative
        return Derivative(self.astype(Sum), x, evaluate=True).simplify()
        
    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices):
        return self.func(self.arg[indices])
        
    def simplify(self, deep=False, **kwargs):
        if self.arg.is_Stack:
            if len(self.arg.limits) == 1 and not self.arg.variable.shape:
                function = self.arg.expr
                self = Sum(function, *self.arg.limits).simplify(**kwargs)
        elif self.arg.is_Piecewise:
            self = self.arg.func(*((self.func(e).simplify(), c) for e, c in self.arg.args)).simplify()
        elif self.arg.is_Mul:
            args = []
            coeff = []
            for arg in self.arg.args:
                if arg.shape:
                    args.append(arg)
                else:
                    coeff.append(arg)
                                
            if coeff:
                coeff = self.arg.func(*coeff)
                function = self.arg.func(*args)
                return coeff * self.func(function)
        return self
    

class ReducedMean(Reduced):
    r"""Represents unevaluated reduced mean.
    input must be a multi-dimensional tensor
    """
    is_complex = True
    
    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.arg.is_zero:
            return True
        
        if self.arg.is_extended_positive or self.arg.is_extended_negative:
            return False

    def doit(self, **hints):
        deep = hints.get('deep', True)
        if deep:
            f = self.arg.doit(**hints)
        else:
            f = self.arg

        if f.is_FiniteSet:
            x, *args = f.args
            rest = f.func(*args)
            from sympy import NotElement, Bool
            sgm = x * Bool(NotElement(x, rest).simplify()).simplify()
            if not rest:
                return sgm
            return self.func(rest).doit(deep=deep) + sgm
        else:
            return self

    @property
    def dtype(self):
        return self.arg.dtype

    def _sympystr(self, p):
        return 'ReducedMean(%s)' % p._print(self.arg)

    def _lean(self, p):
        return 'ReducedMean(%s)' % p._print(self.arg)
    
    def _latex(self, p, exp=None):
        expr = p._print(self.arg)
        if self.arg.is_Add or self.arg.is_MatMul:
            expr = r"\left(%s\right)" % expr
        expr = r"\sum{%s}" % expr
        if exp is None:
            return expr
        return r"\left(%s\right)^{%s}" % (expr, exp)
    
    def _eval_is_finite(self):
        return self.arg.is_finite

    def _eval_is_extended_real(self):
        return self.arg.is_extended_real

    def _eval_is_extended_positive(self):
        return self.arg.is_extended_positive
    
    def _eval_is_extended_negative(self):
        return self.arg.is_extended_negative

    def _eval_exp(self):
        from sympy import log
        from sympy.concrete.products import Product
        if isinstance(self.arg, log):
            return Product(self.arg.arg, *self.limits)

    def _eval_derivative(self, x):
        from sympy.core.function import Derivative
        return Derivative(self.astype(Sum), x, evaluate=True).simplify()
        
    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices):
        return self.func(self.arg[indices])
        
    def simplify(self, deep=False, **kwargs):
        if self.arg.is_Piecewise:
            self = self.arg.func(*((self.func(e).simplify(), c) for e, c in self.arg.args)).simplify()
        elif self.arg.is_Mul:
            args = []
            coeff = []
            for arg in self.arg.args:
                if arg.shape:
                    args.append(arg)
                else:
                    coeff.append(arg)
                                
            if coeff:
                coeff = self.arg.func(*coeff)
                function = self.arg.func(*args)
                return coeff * self.func(function)
        return self

    

class ReducedMinMaxBase(Reduced):

    is_extended_real = True

    def _eval_is_zero(self):
        if self.arg.is_zero:
            return True
        
        if self.arg.is_extended_positive or self.arg.is_extended_negative:
            return False
        
    def doit(self, **hints):
        deep = hints.get('deep', True)
        if deep:
            f = self.arg.doit(**hints)
        else:
            f = self.arg

        if f.is_FiniteSet:
            x, *args = f.args
            rest = f.func(*args)
            from sympy import NotElement, Bool
            sgm = x * Bool(NotElement(x, rest).simplify()).simplify()
            if not rest:
                return sgm
            return self.func(rest).doit(deep=deep) + sgm
        else:
            return self

    @property
    def dtype(self):
        expr = self.arg
        if expr.is_set:
            return expr.etype
        return expr.dtype

    def _sympystr(self, p):
        return '%s(%s)' % (self.__class__.__name__, p._print(self.arg))

    def _lean(self, p):
        return '%s(%s)' % (self.__class__.__name__, p._print(self.arg))
    
    def _latex(self, p, exp=None):
        expr = p._print(self.arg)
        name = self.__class__.__name__[-3:].lower()
        if self.arg.is_Add or self.arg.is_MatMul:
            expr = r"\left(%s\right)" % expr
        expr = "\\%s{%s}" % (name, expr)
        if exp is None:
            return expr
        return r"\left(%s\right)^{%s}" % (expr, exp)
    
    def _eval_is_finite(self):
        return self.arg.is_finite

    def _eval_is_extended_integer(self):
        return self.arg.is_extended_integer

    def _eval_is_extended_real(self):
        return self.arg.is_extended_real

    def _eval_is_extended_positive(self):
        return self.arg.is_extended_positive
    
    def _eval_is_extended_negative(self):
        return self.arg.is_extended_negative

    def _eval_exp(self):
        from sympy import log
        from sympy.concrete.products import Product
        if isinstance(self.arg, log):
            return Product(self.arg.arg, *self.limits)

    def _eval_derivative(self, x):
        from sympy.core.function import Derivative
        return Derivative(self.astype(Sum), x, evaluate=True).simplify()
        
    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices):
        return self.func(self.arg[indices])
        
    def simplify(self, deep=False, **kwargs):
        if self.arg.is_Stack:
            if len(self.arg.limits) == 1 and not self.arg.variable.shape:
                function = self.arg.expr
                self = self.operator(function, *self.arg.limits).simplify(**kwargs)
        elif self.arg.is_Piecewise:
            self = self.arg.func(*((self.func(e).simplify(), c) for e, c in self.arg.args)).simplify()
        elif self.arg.is_Mul:
            args = []
            coeff = []
            for arg in self.arg.args:
                if arg.shape:
                    args.append(arg)
                else:
                    coeff.append(arg)
                                
            if coeff:
                coeff = self.arg.func(*coeff)
                function = self.arg.func(*args)
                return coeff * self.func(function)
        return self

    @classmethod
    def eval(cls, arg, axis=-1):
        if axis == arg.default_axis:
            if not arg.shape and not arg.is_set:
                return arg


class ReducedMin(ReducedMinMaxBase):
    r"""Represents unevaluated reduced minimize.
    input must be a multi-dimensional tensor
    """

    operator = Minima


class ReducedMax(ReducedMinMaxBase):
    r"""Represents unevaluated reduced maximize.
    input must be a multi-dimensional tensor
    """
    operator = Maxima    


class ReducedArgMinMaxBase(Reduced):
    r"""Represents unevaluated reduced ArgMax / ArgMin.
    input must be a multi-dimensional tensor
    """
    
    is_integer = True
    
    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        return dtype.integer

    def _sympystr(self, p):
        return '%s(%s)' % (self.__class__.__name__, p._print(self.arg))

    def _lean(self, p):
        return '%s(%s)' % (self.__class__.__name__, p._print(self.arg))
    
    def _latex(self, p, exp=None):
        name = self.__class__.__name__.lower()[-3:]
        tex = r'\mathop{{\rm %s}^{-1}}' % name
        
        if self.arg.is_Add:
            tex += r"\left(%s\right)" % p._print(self.arg)
        else:
            tex += p._print(self.arg)

        return tex
    
    def _eval_is_finite(self):
        return True

    def _eval_is_extended_real(self):
        return True

    def _eval_is_extended_positive(self):
        ...
    
    def _eval_is_extended_negative(self):
        return False

    def _eval_is_extended_nonnegative(self):
        return True
        
    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices):
        return self.func(self.arg[indices])
        
    def simplify(self, deep=False, **kwargs):
        return self

    def monotonicity(self, x):
        n = self.arg.shape[-1]
        if n >= 1:
            return (S.Zero, S(self.arg.shape[-1] - 1)), 0
        return super().monotonicity(x)

    def _has(self, pattern):
        n = self.arg.shape[-1]
        if not isinstance(n, int):
            if n._has(pattern):
                return True
            
        return super()._has(pattern)


class ReducedArgMax(ReducedArgMinMaxBase):
    r"""Represents unevaluated reduced ArgMax.
    input must be a multi-dimensional tensor
    """
    
    @classmethod
    def eval(cls, arg, axis=-1):
        if axis == arg.default_axis:
            return arg._eval_ReducedArgMax()


class ReducedArgMin(ReducedArgMinMaxBase):
    r"""Represents unevaluated reduced ArgMin.
    input must be a multi-dimensional tensor
    """
    
    @classmethod
    def eval(cls, arg, axis=-1):
        if axis == arg.default_axis:
            return arg._eval_ReducedArgMin()
