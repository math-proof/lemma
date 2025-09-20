from sympy.core import S, Add, Mul, sympify, Symbol, Dummy, Basic
from sympy.core.expr import Expr
from sympy.core.exprtools import factor_terms
from sympy.core.function import (Function, Derivative, ArgumentIndexError,
    AppliedUndef)
from sympy.core.logic import fuzzy_not, fuzzy_or
from sympy.core.numbers import pi, I, oo
from sympy.core.relational import Eq
from sympy.functions.elementary.exponential import exp, exp_polar, log
from sympy.functions.elementary.integers import ceil
from sympy.core.power import sqrt
from sympy.functions.elementary.piecewise import Piecewise
from sympy.functions.elementary.trigonometric import atan, atan2
from sympy.core.cache import cacheit

###############################################################################
######################### REAL and IMAGINARY PARTS ############################
###############################################################################


class Re(Function):
    """
    Returns real part of expression. This function performs only
    elementary analysis and so it will fail to decompose properly
    more complicated expressions. If completely simplified result
    is needed then use Basic.as_real_imag() or perform complex
    expansion on instance of this function.

    Examples
    ========

    >>> from sympy.abc import x, y
    >>> Re(2*E)
    2*E
    >>> Re(2*I + 17)
    17
    >>> Re(2*I)
    0
    >>> Re(Im(x) + x*I + 2)
    2

    See Also
    ========
    Im
    """

    is_extended_real = True
    unbranched = True  # implicitly works on the projection to C

    @classmethod
    def eval(cls, arg, **options):
        if arg is S.NaN:
            return S.NaN
        if arg is S.ComplexInfinity:
            return S.NaN
        if arg.is_super_real:
            return arg
        if arg.is_imaginary or (S.ImaginaryUnit * arg).is_extended_real:
            return S.Zero
        if arg.is_DenseMatrix:
            return arg.as_real_imag()[0]
        if arg.is_MatMul:
            return
        if arg.is_Mul:
            import std
            reals, unreals = std.array_split(arg.args, lambda x: x.is_super_real)
            if reals:
                return cls(Mul(*unreals)) * Mul(*reals)
            return

        if arg.is_Conjugate:
            return cls(arg.arg)

        if arg.is_Exp:
            exp = arg.arg / S.ImaginaryUnit
            if exp.is_super_real:
                from sympy import cos
                return cos(exp)
            return

        included, reverted, excluded = [], [], []
        args = Add.make_args(arg)
        for term in args:
            coeff = term.as_coefficient(S.ImaginaryUnit)

            if coeff is not None:
                if not coeff.is_extended_real:
                    reverted.append(coeff)
            elif not term.has(S.ImaginaryUnit) and term.is_extended_real:
                excluded.append(term)
            else:
                # Try to do some advanced expansion.  If
                # impossible, don't try to do Re(arg) again
                # (because this is what we are trying to do now).
                real_imag = term.as_real_imag(ignore=arg)
                if real_imag:
                    excluded.append(real_imag[0])
                else:
                    included.append(term)

        if len(args) != len(included):
            a, b, c = (Add(*xs) for xs in [included, reverted, excluded])

            return cls(a) - Im(b) + c

    def as_real_imag(self, deep=True, **hints):
        """
        Returns the real number with a zero imaginary part.
        """
        return self, S.Zero

    def _eval_derivative(self, x):
        if x.is_extended_real or self.args[0].is_extended_real:
            return Re(Derivative(self.args[0], x, evaluate=True))
        if x.is_imaginary or self.args[0].is_imaginary:
            return -S.ImaginaryUnit \
                * Im(Derivative(self.args[0], x, evaluate=True))

    def _eval_rewrite_as_im(self, arg, **kwargs):
        return self.args[0] - S.ImaginaryUnit * Im(self.args[0])

    def _eval_is_algebraic(self):
        return self.args[0].is_algebraic

    def _eval_is_zero(self):
        # is_imaginary implies nonzero
        return fuzzy_or([self.args[0].is_imaginary, self.args[0].is_zero])

    def _eval_is_finite(self):
        if self.args[0].is_finite:
            return True

    def _eval_is_extended_complex(self):
        return self.arg.is_extended_complex


    def _latex(self, p, exp=None):
        from sympy.printing.precedence import PRECEDENCE
        if p._settings['gothic_re_im']:
            tex = r"\Re{%s}" % p.parenthesize(self.args[0], PRECEDENCE['Atom'])
        else:
            tex = r"\operatorname{{Re}}{{{}}}".format(p.parenthesize(self.args[0], PRECEDENCE['Atom']))

        return p._do_exponent(tex, exp)

    @classmethod
    def sub_class_key(cls):
        return 41


class Im(Function):
    """
    Returns imaginary part of expression. This function performs only
    elementary analysis and so it will fail to decompose properly more
    complicated expressions. If completely simplified result is needed then
    use Basic.as_real_imag() or perform complex expansion on instance of
    this function.

    Examples
    ========

    >>> from sympy.abc import x, y
    >>> Im(2*E)
    0
    >>> Re(2*I + 17)
    17
    >>> Im(x*I)
    Re(x)
    >>> Im(Re(x) + y)
    Im(y)

    See Also
    ========

    Re
    """

    is_extended_real = True
    unbranched = True  # implicitly works on the projection to C

    @classmethod
    def eval(cls, arg, **options):
        if arg is S.NaN:
            return S.NaN

        if arg is S.ComplexInfinity:
            return S.NaN

        if arg.is_extended_real:
            return S.Zero

        if arg.is_imaginary or (S.ImaginaryUnit * arg).is_extended_real:
            return -S.ImaginaryUnit * arg

        if arg.is_DenseMatrix:
            return arg.as_real_imag()[1]

        if arg.is_MatMul:
            return

        if arg.is_Conjugate:
            return -Im(arg.arg)

        included, reverted, excluded = [], [], []
        args = Add.make_args(arg)
        for term in args:
            coeff = term.as_coefficient(S.ImaginaryUnit)

            if coeff is not None:
                if not coeff.is_extended_real:
                    reverted.append(coeff)
                else:
                    excluded.append(coeff)
            elif term.has(S.ImaginaryUnit) or not term.is_extended_real:
                # Try to do some advanced expansion.  If
                # impossible, don't try to do Im(arg) again
                # (because this is what we are trying to do now).
                real_imag = term.as_real_imag(ignore=arg)
                if real_imag:
                    excluded.append(real_imag[1])
                else:
                    included.append(term)

        if len(args) != len(included):
            a, b, c = (Add(*xs) for xs in [included, reverted, excluded])

            return cls(a) + Re(b) + c

    def as_real_imag(self, deep=True, **hints):
        """
        Return the imaginary part with a zero real part.

        Examples
        ========

        >>> from sympy.functions import Im
        >>> from sympy import I
        >>> Im(2 + 3*I).as_real_imag()
        (3, 0)
        """
        return self, S.Zero

    def _eval_derivative(self, x):
        if x.is_extended_real or self.args[0].is_extended_real:
            return Im(Derivative(self.args[0], x, evaluate=True))
        if x.is_imaginary or self.args[0].is_imaginary:
            return -S.ImaginaryUnit \
                * Re(Derivative(self.args[0], x, evaluate=True))

    def _eval_rewrite_as_re(self, arg, **kwargs):
        return -S.ImaginaryUnit * (self.args[0] - Re(self.args[0]))

    def _eval_is_algebraic(self):
        return self.args[0].is_algebraic

    def _eval_is_zero(self):
        return self.args[0].is_extended_real

    def _eval_is_finite(self):
        if self.args[0].is_finite:
            return True

    def _eval_is_extended_complex(self):
        return self.arg.is_extended_complex

    def _latex(self, p, exp=None):
        from sympy.printing.precedence import PRECEDENCE
        if p._settings['gothic_re_im']:
            tex = r"\Im{%s}" % p.parenthesize(self.args[0], PRECEDENCE['Atom'])
        else:
            tex = r"\operatorname{{Im}}{{{}}}".format(p.parenthesize(self.args[0], PRECEDENCE['Atom']))

        return p._do_exponent(tex, exp)

    @classmethod
    def sub_class_key(cls):
        return 42

###############################################################################
############### SIGN, ABSOLUTE VALUE, ARGUMENT and CONJUGATION ################
###############################################################################


class Sign(Function):
    """
    Returns the complex sign of an expression:

    If the expression is real the sign will be:

        * 1 if expression is positive
        * 0 if expression is equal to zero
        * -1 if expression is negative

    If the expression is imaginary the sign will be:

        * I if Im(expression) is positive
        * -I if Im(expression) is negative

    Otherwise an unevaluated expression will be returned. When evaluated, the
    result (in general) will be ``cos(arg(expr)) + I*sin(arg(expr))``.

    Examples
    ========

    >>> from sympy.functions import sign
    >>> from sympy.core.numbers import I

    >>> sign(-1)
    -1
    >>> sign(0)
    0
    >>> sign(-3*I)
    -I
    >>> sign(1 + I)
    sign(1 + I)
    >>> _.evalf()
    0.707106781186548 + 0.707106781186548*I

    See Also
    ========

    Abs, conjugate
    """

    is_finite = True
    is_complex = True

    def doit(self, **hints):
        if self.args[0].is_zero == False:
            return self.args[0] / Abs(self.args[0])
        return self

    @classmethod
    def eval(cls, arg):
        # handle what we can
        if arg.is_Mul:
            c, args = arg.as_coeff_mul()
            unk = []
            s = sign(c)
            for a in args:
                if a.is_extended_negative:
                    s = -s
                elif a.is_extended_positive:
                    pass
                else:
                    ai = Im(a)
                    if a.is_imaginary and ai.is_comparable:  # i.e. a = I*real
                        s *= S.ImaginaryUnit
                        if ai.is_extended_negative:
                            # can't use sign(ai) here since ai might not be
                            # a Number
                            s = -s
                    else:
                        unk.append(a)
            if c is S.One and len(unk) == len(args):
                return None
            return s * cls(arg._new_rawargs(*unk))
        if arg is S.NaN:
            return S.NaN
        
        if arg.is_DenseMatrix:
            from sympy import Matrix
            return Matrix(*(Sign(arg) for arg in arg.args), shape=arg.shape)
            
        if arg.is_zero:  # it may be an Expr that is zero
            return S.Zero
        if arg.is_extended_positive:
            return S.One
        if arg.is_extended_negative:
            return S.NegativeOne
        if arg.is_Function:
            if isinstance(arg, sign):
                return arg
        if arg.is_imaginary:
            if arg.is_Pow and arg.exp is S.Half:
                # we catch this because non-trivial sqrt args are not expanded
                # e.g. sqrt(1-sqrt(2)) --x-->  to I*sqrt(sqrt(2) - 1)
                return S.ImaginaryUnit
            arg2 = -S.ImaginaryUnit * arg
            if arg2.is_extended_positive:
                return S.ImaginaryUnit
            if arg2.is_extended_negative:
                return -S.ImaginaryUnit

    def _eval_Abs(self):
        if fuzzy_not(self.args[0].is_zero):
            return S.One

    def _eval_conjugate(self):
        return sign(conjugate(self.args[0]))

    def _eval_derivative(self, x):
        if self.args[0].is_extended_real:
            from sympy.functions.special.delta_functions import DiracDelta
            return 2 * Derivative(self.args[0], x, evaluate=True) \
                * DiracDelta(self.args[0])
        elif self.args[0].is_imaginary:
            from sympy.functions.special.delta_functions import DiracDelta
            return 2 * Derivative(self.args[0], x, evaluate=True) \
                * DiracDelta(-S.ImaginaryUnit * self.args[0])

    def _eval_is_extended_negative(self):
        if self.args[0].is_extended_negative:
            return True

    def _eval_is_extended_positive(self):
        if self.args[0].is_extended_positive:
            return True

    def _eval_is_imaginary(self):
        return self.arg.is_imaginary

    def _eval_is_finite(self):
        return self.arg.is_finite

    def _eval_is_extended_integer(self):
        return self.arg.is_extended_real

    def _eval_is_zero(self):
        return self.arg.is_zero

    def _eval_power(self, other):
        if (
            fuzzy_not(self.args[0].is_zero) and
            other.is_integer and
            other.is_even
        ):
            return S.One

    def _eval_rewrite_as_Piecewise(self, arg, **kwargs):
        if arg.is_extended_real:
            return Piecewise((1, arg > 0), (-1, arg < 0), (0, True))

    def _eval_rewrite_as_Heaviside(self, arg, **kwargs):
        from sympy.functions.special.delta_functions import Heaviside
        if arg.is_extended_real:
            return Heaviside(arg) * 2 - 1

    def _eval_simplify(self, ratio, measure, rational, inverse):
        return self.func(self.args[0].factor())

    def _latex(self, p, exp=None):
        tex = r"sign\left({%s}\right)" % p._print(self.args[0])
        if exp is not None:
            return r"%s^{%s}" % (tex, exp)
        else:
            return tex

    def _sympystr(self, p):
        return "sign(%s)" % p._print(self.arg)

    def _lean(self, p):
        return "sign(%s)" % p._print(self.arg)

    def __iter__(self):
        raise TypeError

    def __getitem__(self, index):
        return self.func(self.arg[index])

sign = Sign

class Abs(Function):
    """
    Return the absolute value of the argument.

    This is an extension of the built-in function abs() to accept symbolic
    values.  If you pass a SymPy expression to the built-in abs(), it will
    pass it automatically to Abs().

    Examples
    ========

    >>> from sympy import Abs, Symbol, S
    >>> Abs(-1)
    1
    >>> x = Symbol('x', real=True)
    >>> Abs(-x)
    Abs(x)
    >>> Abs(x**2)
    x**2
    >>> abs(-x) # The Python built-in
    Abs(x)

    Note that the Python built-in will return either an Expr or int depending on
    the argument::

        >>> type(abs(-1))
        <... 'int'>
        >>> type(abs(S.NegativeOne))
        <class 'sympy.core.numbers.One'>

    Abs will always return a sympy object.

    See Also
    ========

    sign, conjugate
    """

    is_extended_real = True
    is_extended_negative = False
    unbranched = True

    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        return dtype.real(nonnegative=True)

    def fdiff(self, argindex=1):
        """
        Get the first derivative of the argument to Abs().

        Examples
        ========

        >>> from sympy.abc import x
        >>> from sympy.functions import Abs
        >>> Abs(-x).fdiff()
        sign(x)
        """
        if argindex == 1:
            return sign(self.args[0])
        else:
            raise ArgumentIndexError(self, argindex)

    @classmethod
    def eval(cls, arg):
        from sympy.simplify.simplify import signsimp
        from sympy.core.function import expand_mul

        if hasattr(arg, '_eval_Abs'):
            obj = arg._eval_Abs()
            if obj is not None:
                return obj
        # handle what we can
        arg = signsimp(arg, evaluate=False)
        if arg is S.NaN:
            return S.NaN
        if arg is S.ComplexInfinity:
            return S.Infinity
        if isinstance(arg, exp):
            return exp(Re(arg.args[0]))
        if isinstance(arg, AppliedUndef):
            return
        if arg.is_MatMul:
            return

        if arg.is_zero:
            return S.Zero
        if arg.is_extended_nonnegative:
            return arg
        if arg.is_extended_nonpositive:
            return -arg
        if arg.is_imaginary:
            arg2 = -S.ImaginaryUnit * arg
            if arg2.is_extended_nonnegative:
                return arg2
        # reject result if all new conjugates are just wrappers around
        # an expression that was already in the arg
        conj = signsimp(arg.conjugate(), evaluate=False)
        new_conj = conj.atoms(conjugate) - arg.atoms(conjugate)
        if new_conj and all(arg.has(i.args[0]) for i in new_conj):
            return
        if arg != conj and arg != -conj:
            ignore = arg.atoms(Abs)
            abs_free_arg = arg.xreplace({i: Dummy(real=True) for i in ignore})
            unk = [a for a in abs_free_arg.free_symbols if a.is_extended_real is None]
            if not unk or not all(conj.has(conjugate(u)) for u in unk):
                return sqrt(expand_mul(arg * conj))

    def _eval_is_zero(self):
        return self._args[0].is_zero

    def _eval_is_extended_integer(self):
        return self.arg.is_extended_integer

    def _eval_is_extended_positive(self):
        is_z = self.is_zero
        if is_z is not None:
            return not is_z

    def _eval_is_rational(self):
        if self.arg.is_set:
            return True
        return self.args[0].is_rational

    def _eval_is_finite(self):
        return self.arg.is_finite

    def _eval_is_even(self):
        if self.args[0].is_extended_real:
            return self.args[0].is_even

    def _eval_is_algebraic(self):
        return self.args[0].is_algebraic

    def _eval_power(self, exponent):
        x = self.args[0]
        if x.is_extended_real and exponent.is_integer:
            if exponent.is_even:
                return x ** exponent
            elif exponent is not S.NegativeOne and exponent.is_Integer:
                return x ** (exponent - 1) * self
        elif exponent.is_Rational:
            q = exponent.q
            if x.is_Pow:
                b, e = x.args
                if q > 1 and not e % q: 
                    x = b ** (e / q)                    
                    return abs(x) ** exponent.p
            elif x.is_Mul:
                args = []
                for t in x.args:
                    if not t.is_Pow:
                        break
                    b, e = t.args
                    if e % q:
                        break
                    
                    t = b ** (e / q)
                    args.append(t)
                else:
                    x = Mul(*args)
                    return abs(x) ** exponent.p
        return

    def _eval_nseries(self, x, n, logx):
        direction = self.args[0].leadterm(x)[0]
        s = self.args[0]._eval_nseries(x, n=n, logx=logx)
        when = Eq(direction, 0)
        return Piecewise(
            ((s.subs(direction, 0)), when),
            (sign(direction) * s, True),
        )

    def _eval_derivative(self, x):
        if self.args[0].is_extended_real or self.args[0].is_imaginary:
            return Derivative(self.args[0], x, evaluate=True) \
                * sign(conjugate(self.args[0]))
        rv = (Re(self.args[0]) * Derivative(Re(self.args[0]), x,
            evaluate=True) + Im(self.args[0]) * Derivative(Im(self.args[0]),
                x, evaluate=True)) / Abs(self.args[0])
        return rv.rewrite(sign)

    def _eval_rewrite_as_Heaviside(self, arg, **kwargs):
        # Note this only holds for real arg (since Heaviside is not defined
        # for complex arguments).
        from sympy.functions.special.delta_functions import Heaviside
        if arg.is_extended_real:
            return arg * (Heaviside(arg) - Heaviside(-arg))

    def _eval_rewrite_as_Piecewise(self, arg, **kwargs):
        if arg.is_extended_real:
            return Piecewise((arg, arg >= 0), (-arg, True))

    def _eval_rewrite_as_sign(self, arg, **kwargs):
        return arg / sign(arg)

    def min(self):
        x = self.arg
        if not x.is_set:
            if x >= 0:
                return x.min()
            if x <= 0:
                return abs(x.max())
        return S.Zero
    
    def _sympystr(self, p):
        return "abs(%s)" % p._print(self.arg)
    
    def _lean(self, p):
        return "|%s|" % p._print(self.arg)
    
    def _latex(self, p, exp=None):
        tex = r"\left|{%s}\right|" % p._print(self.args[0])

        if exp is not None:
            return r"%s^{%s}" % (tex, exp)
        else:
            return tex

    def __iter__(self):
        raise TypeError

    def __getitem__(self, index):
        return self.func(self.arg[index])

    @classmethod
    def _eval_simplify_Lamda(cls, self, squeeze=False):
        return exp._eval_simplify_Lamda(self)


class Norm(Function):
    """
    Return the norm value of a vector.

    """

    is_extended_real = True
    is_extended_negative = False
    is_extended_nonnegative = True
    unbranched = True

    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        return dtype.real(nonnegative=True)

    @cacheit
    def _eval_shape(self):
        return self.arg.shape[:-1]
    
    def fdiff(self, argindex=1):
        """
        Get the first derivative of the argument to Abs().

        Examples
        ========

        >>> from sympy.abc import x
        >>> from sympy.functions import Abs
        >>> Abs(-x).fdiff()
        sign(x)
        """
        if argindex == 1:
            return sign(self.args[0])
        else:
            raise ArgumentIndexError(self, argindex)

    @classmethod
    def eval(cls, arg):
        if hasattr(arg, '_eval_Norm'):
            obj = arg._eval_Norm()
            if obj is not None:
                return obj

    def _eval_is_zero(self):
        return self.arg.is_zero

    def _eval_is_extended_positive(self):
        is_z = self.is_zero
        if is_z is not None:
            return not is_z

    def _eval_is_rational(self):
        if self.arg.is_set:
            return True
        return self.args[0].is_rational

    def _eval_is_finite(self):
        return self.arg.is_finite

    def _eval_is_even(self):
        if self.args[0].is_extended_real:
            return self.args[0].is_even

    def _eval_is_algebraic(self):
        return self.args[0].is_algebraic

    def _eval_derivative(self, x):
        ...

    def _eval_rewrite_as_Heaviside(self, arg, **kwargs):
        ...

    def _eval_rewrite_as_Piecewise(self, arg, **kwargs):
        ...

    def _eval_rewrite_as_sign(self, arg, **kwargs):
        ...

    def _sympystr(self, p):
        return "Norm(%s)" % p._print(self.arg)

    def _lean(self, p):
        return "‖%s‖" % p._print(self.arg)

    def _latex(self, p, exp=None):
        left_vert = r"\left|\kern-0.25ex" * 2
#         left_vert = r"\left\vert\kern-0.25ex" * 2
        right_vert = r"\right|\kern-0.25ex" * 2
#         right_vert = r"\right\vert\kern-0.25ex" * 2

        latex = r"%s{%s}%s" % (left_vert, p._print(self.arg), right_vert)
        if exp is not None:
            latex = "{%s}^{%s}" % (latex, p._print(exp))
        return latex

    def simplify(self, deep=False, **kwargs):
        if self.arg.is_Mul:
            coeff = []
            args = []
            for arg in self.arg.args:
                if arg.shape:
                    args.append(arg)
                else:
                    coeff.append(arg)
            if coeff:
                Mul = self.arg.func
                return abs(Mul(*coeff)) * self.func(Mul(*args))
        return Function.simplify(self, deep=deep, **kwargs)
    
    def _subs(self, old, new, **hints):
        arg = self.arg
        try:
            arg = arg._subs(old, new)
            if self.arg == arg:
                return self
        except Exception as e:
            if str(e) == 'empty slices':
                if any(s._has(old) for s in arg.shape):
                    from sympy import Zeros
                    return Zeros(*self.shape)
            
            raise e
        if len(arg.shape) < len(self.arg.shape):
            return abs(arg)
        return self.func(arg)
        
    
class Arg(Function):
    """
    Returns the argument (in radians) of a complex number. For a positive
    number, the argument is always 0.

    Examples
    ========

    >>> from sympy.functions import arg
    >>> from sympy import I, sqrt
    >>> arg(2.0)
    0
    >>> arg(I)
    pi/2
    >>> arg(sqrt(2) + I*sqrt(2))
    pi/4

    """

    is_extended_real = True
    is_real = True
    is_finite = True

    @classmethod
    def eval(cls, arg):
        if isinstance(arg, exp_polar):
            return periodic_argument(arg, oo)
        if not arg.is_Atom:
            c, arg_ = factor_terms(arg).as_coeff_Mul()
            if arg_.is_Mul:
                arg_ = Mul(*[a if (sign(a) not in (-1, 1)) else
                    sign(a) for a in arg_.args])
            arg_ = sign(c) * arg_
        else:
            arg_ = arg
        if arg_.atoms(AppliedUndef):
            return
        x, y = arg_.as_real_imag()
        rv = atan2(y, x)
        if rv.is_number:
            return rv
        if arg_ != arg:
            return cls(arg_, evaluate=False)

    def _eval_derivative(self, t):
        x, y = self.args[0].as_real_imag()
        return (x * Derivative(y, t, evaluate=True) - y * 
                    Derivative(x, t, evaluate=True)) / (x ** 2 + y ** 2)

    def _eval_rewrite_as_atan2(self, arg, **kwargs):
        x, y = self.args[0].as_real_imag()
        return atan2(y, x)
    
    @property
    def domain(self):
        from sympy import Interval
        return Interval(-S.Pi, S.Pi, left_open=True)

    def simplify(self, deep=False, **kwargs):
        expri = self.arg
        if expri.is_Exp:
            i_exp = expri.arg
            if i_exp.is_Mul:
                args = i_exp.args
                if len(args) == 2:
                    i, arg = args
                    if i.is_ImaginaryUnit:
                        if arg.is_Arg:
#                             Arg(exp(i * Arg(z))) = Arg(z)
                            return arg
            
        return Function.simplify(self, deep, **kwargs)
    
    @classmethod
    def sub_class_key(cls):
        return 43
    
    def _latex(self, p, exp=None):
        arg = self.arg
        if arg.is_Mul or arg.is_Add:
            arg = r"\left(%s\right)" % p._print(arg)
        else:
            arg = p._print(arg)
        tex = r"\arg {%s}" % arg
        if exp is not None:
            return r"%s^{%s}" % (tex, exp)
        else:
            return tex
    
    def _sympystr(self, p):
        return "arg(%s)" % p._print(self.arg)

    def _lean(self, p):
        return "arg %s" % p._print(self.arg)


arg = Arg

class Conjugate(Function):
    """
    Returns the `complex conjugate` Ref[1] of an argument.
    In mathematics, the complex conjugate of a complex number
    is given by changing the sign of the imaginary part.

    Thus, the conjugate of the complex number
    :math:`a + ib` (where a and b are real numbers) is :math:`a - ib`

    Examples
    ========

    >>> from sympy import conjugate, I
    >>> conjugate(2)
    2
    >>> conjugate(I)
    -I

    See Also
    ========

    sign, Abs

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Complex_conjugation
    """

    @classmethod
    def eval(cls, arg):
        obj = arg._eval_conjugate()
        if obj is not None:
            return obj

    def _eval_Abs(self):
        return Abs(self.args[0], evaluate=True)

    def _eval_adjoint(self):
        return transpose(self.args[0])

    def _eval_conjugate(self):
        return self.args[0]

    def _eval_derivative(self, x):
        if x.is_real:
            return conjugate(Derivative(self.args[0], x, evaluate=True))
        elif x.is_imaginary:
            return -conjugate(Derivative(self.args[0], x, evaluate=True))

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            from sympy import Adjoint
            return Adjoint(self.args[0])

    def _eval_is_algebraic(self):
        return self.args[0].is_algebraic

    def _eval_is_finite(self):
        return self.arg.is_finite
    
    def _eval_is_extended_integer(self):
        return self.arg.is_extended_integer
    
    def _eval_is_super_integer(self):
        return self.arg.is_super_integer
    
    def _eval_is_extended_rational(self):
        return self.arg.is_extended_rational
    
    def _eval_is_hyper_rational(self):
        return self.arg.is_hyper_rational
    
    def _eval_is_super_rational(self):
        return self.arg.is_super_rational
    
    def _eval_is_extended_real(self):
        return self.arg.is_extended_real
    
    def _eval_is_hyper_real(self):
        return self.arg.is_hyper_real
    
    def _eval_is_super_real(self):
        return self.arg.is_super_real
    
    def _eval_is_extended_complex(self):
        return self.arg.is_extended_complex
    
    def _eval_is_hyper_complex(self):
        return self.arg.is_hyper_complex
    
    def _latex(self, p, exp=None):
        tex = r"\overline{%s}" % p._print(self.args[0])

        if exp is not None:
            return r"%s^{%s}" % (tex, exp)
        else:
            return tex

    def _sympystr(self, p):
        x = self.arg
        
        s = p._print(x)
        if x.is_AssocOp or x.is_MatMul:
            s = "(%s)" % s
        return "~%s" % s

    def _lean(self, p):
        x = self.arg
        
        s = p._print(x)
        if x.is_AssocOp or x.is_MatMul:
            s = "(%s)" % s
        return "~%s" % s

    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices):
        return self.func(self.arg[indices])

    @classmethod
    def _eval_simplify_Lamda(cls, self, squeeze=False):
        return exp._eval_simplify_Lamda(self)

    @classmethod
    def sub_class_key(cls):
        return 40

    def domain_definition(self, allow_empty=False):
        return self.arg.domain_definition(allow_empty=allow_empty)


conjugate = Conjugate

###############################################################################
############### HANDLING OF POLAR NUMBERS #####################################
###############################################################################


class polar_lift(Function):
    """
    Lift argument to the Riemann surface of the logarithm, using the
    standard branch.

    >>> from sympy import Symbol, polar_lift, I
    >>> p = Symbol('p', polar=True)
    >>> x = Symbol('x')
    >>> polar_lift(4)
    4*exp_polar(0)
    >>> polar_lift(-4)
    4*exp_polar(I*pi)
    >>> polar_lift(-I)
    exp_polar(-I*pi/2)
    >>> polar_lift(I + 2)
    polar_lift(2 + I)

    >>> polar_lift(4*x)
    4*polar_lift(x)
    >>> polar_lift(4*p)
    4*p

    See Also
    ========

    sympy.functions.elementary.exponential.exp_polar
    periodic_argument
    """

    is_polar = True
    is_comparable = False  # Cannot be evalf'd.

    @classmethod
    def eval(cls, arg):
        from sympy.functions.elementary.complexes import arg as argument
        if arg.is_number:
            ar = argument(arg)
            # In general we want to affirm that something is known,
            # e.g. `not ar.has(argument) and not ar.has(atan)`
            # but for now we will just be more restrictive and
            # see that it has evaluated to one of the known values.
            if ar in (0, pi / 2, -pi / 2, pi):
                return exp_polar(I * ar) * abs(arg)

        if arg.is_Mul:
            args = arg.args
        else:
            args = [arg]
        included = []
        excluded = []
        positive = []
        for arg in args:
            if arg.is_polar:
                included += [arg]
            elif arg.is_positive:
                positive += [arg]
            else:
                excluded += [arg]
        if len(excluded) < len(args):
            if excluded:
                return Mul(*(included + positive)) * polar_lift(Mul(*excluded))
            elif included:
                return Mul(*(included + positive))
            else:
                return Mul(*positive) * exp_polar(0)

    def _eval_evalf(self, prec):
        """ Careful! any evalf of polar numbers is flaky """
        return self.args[0]._eval_evalf(prec)

    def _eval_Abs(self):
        return Abs(self.args[0], evaluate=True)


class periodic_argument(Function):
    """
    Represent the argument on a quotient of the Riemann surface of the
    logarithm. That is, given a period P, always return a value in
    (-P/2, P/2], by using exp(P*I) == 1.

    >>> from sympy import exp, exp_polar, periodic_argument, unbranched_argument
    >>> from sympy import I, pi
    >>> unbranched_argument(exp(5*I*pi))
    pi
    >>> unbranched_argument(exp_polar(5*I*pi))
    5*pi
    >>> periodic_argument(exp_polar(5*I*pi), 2*pi)
    pi
    >>> periodic_argument(exp_polar(5*I*pi), 3*pi)
    -pi
    >>> periodic_argument(exp_polar(5*I*pi), pi)
    0

    See Also
    ========

    sympy.functions.elementary.exponential.exp_polar
    polar_lift : Lift argument to the Riemann surface of the logarithm
    principal_branch
    """

    @classmethod
    def _getunbranched(cls, ar):
        if ar.is_Mul:
            args = ar.args
        else:
            args = [ar]
        unbranched = 0
        for a in args:
            if not a.is_polar:
                unbranched += arg(a)
            elif isinstance(a, exp_polar):
                unbranched += a.exp.as_real_imag()[1]
            elif a.is_Pow:
                re, im = a.exp.as_real_imag()
                unbranched += re * unbranched_argument(
                    a.base) + im * log(abs(a.base))
            elif isinstance(a, polar_lift):
                unbranched += arg(a.args[0])
            else:
                return None
        return unbranched

    @classmethod
    def eval(cls, ar, period):
        # Our strategy is to evaluate the argument on the Riemann surface of the
        # logarithm, and then reduce.
        # NOTE evidently this means it is a rather bad idea to use this with
        # period != 2*pi and non-polar numbers.
        if not period.is_extended_positive:
            return None
        if period == oo and isinstance(ar, principal_branch):
            return periodic_argument(*ar.args)
        if isinstance(ar, polar_lift) and period >= 2 * pi:
            return periodic_argument(ar.args[0], period)
        if ar.is_Mul:
            newargs = [x for x in ar.args if not x.is_positive]
            if len(newargs) != len(ar.args):
                return periodic_argument(Mul(*newargs), period)
        unbranched = cls._getunbranched(ar)
        if unbranched is None:
            return None
        if unbranched.has(periodic_argument, atan2, atan):
            return None
        if period == oo:
            return unbranched
        if period != oo:
            n = ceil(unbranched / period - S(1) / 2) * period
            if not n.has(ceil):
                return unbranched - n

    def _eval_evalf(self, prec):
        z, period = self.args
        if period == oo:
            unbranched = periodic_argument._getunbranched(z)
            if unbranched is None:
                return self
            return unbranched._eval_evalf(prec)
        ub = periodic_argument(z, oo)._eval_evalf(prec)
        return (ub - ceil(ub / period - S(1) / 2) * period)._eval_evalf(prec)


def unbranched_argument(arg):
    return periodic_argument(arg, oo)


class principal_branch(Function):
    """
    Represent a polar number reduced to its principal branch on a quotient
    of the Riemann surface of the logarithm.

    This is a function of two arguments. The first argument is a polar
    number `z`, and the second one a positive real number of infinity, `p`.
    The result is "z mod exp_polar(I*p)".

    >>> from sympy import exp_polar, principal_branch, oo, I, pi
    >>> from sympy.abc import z
    >>> principal_branch(z, oo)
    z
    >>> principal_branch(exp_polar(2*pi*I)*3, 2*pi)
    3*exp_polar(0)
    >>> principal_branch(exp_polar(2*pi*I)*3*z, 2*pi)
    3*principal_branch(z, 2*pi)

    See Also
    ========

    sympy.functions.elementary.exponential.exp_polar
    polar_lift : Lift argument to the Riemann surface of the logarithm
    periodic_argument
    """

    is_polar = True
    is_comparable = False  # cannot always be evalf'd

    @classmethod
    def eval(self, x, period):
        from sympy import oo, exp_polar, I, Mul, polar_lift, Symbol
        if isinstance(x, polar_lift):
            return principal_branch(x.args[0], period)
        if period == oo:
            return x
        ub = periodic_argument(x, oo)
        barg = periodic_argument(x, period)
        if ub != barg and not ub.has(periodic_argument) \
                and not barg.has(periodic_argument):
            pl = polar_lift(x)

            def mr(expr):
                if not isinstance(expr, Symbol):
                    return polar_lift(expr)
                return expr

            pl = pl.replace(polar_lift, mr)
            # Recompute unbranched argument
            ub = periodic_argument(pl, oo)
            if not pl.has(polar_lift):
                if ub != barg:
                    res = exp_polar(I * (barg - ub)) * pl
                else:
                    res = pl
                if not res.is_polar and not res.has(exp_polar):
                    res *= exp_polar(0)
                return res

        if not x.free_symbols:
            c, m = x, ()
        else:
            c, m = x.as_coeff_mul(*x.free_symbols)
        others = []
        for y in m:
            if y.is_positive:
                c *= y
            else:
                others += [y]
        m = tuple(others)
        arg = periodic_argument(c, period)
        if arg.has(periodic_argument):
            return None
        if arg.is_number and (unbranched_argument(c) != arg or
                              (arg == 0 and m != () and c != 1)):
            if arg == 0:
                return abs(c) * principal_branch(Mul(*m), period)
            return principal_branch(exp_polar(I * arg) * Mul(*m), period) * abs(c)
        if arg.is_number and ((abs(arg) < period / 2) == True or arg == period / 2) \
                and m == ():
            return exp_polar(arg * I) * abs(c)

    def _eval_evalf(self, prec):
        from sympy import exp, pi, I
        z, period = self.args
        p = periodic_argument(z, period)._eval_evalf(prec)
        if abs(p) > pi or p == -pi:
            return self  # Cannot evalf for this argument.
        return (abs(z) * exp(I * p))._eval_evalf(prec)


def _polarify(eq, lift, pause=False):
    from sympy import Integral
    if eq.is_polar:
        return eq
    if eq.is_number and not pause:
        return polar_lift(eq)
    if isinstance(eq, Symbol) and not pause and lift:
        return polar_lift(eq)
    elif eq.is_Atom:
        return eq
    elif eq.is_Add:
        r = eq.func(*[_polarify(arg, lift, pause=True) for arg in eq.args])
        if lift:
            return polar_lift(r)
        return r
    elif eq.is_Function:
        return eq.func(*[_polarify(arg, lift, pause=False) for arg in eq.args])
    elif isinstance(eq, Integral):
        # Don't lift the integration variable
        func = _polarify(eq.expr, lift, pause=pause)
        limits = []
        for limit in eq.args[1:]:
            var = _polarify(limit[0], lift=False, pause=pause)
            rest = _polarify(limit[1:], lift=lift, pause=pause)
            limits.append((var,) + rest)
        return Integral(*((func,) + tuple(limits)))
    else:
        return eq.func(*[_polarify(arg, lift, pause=pause)
                         if isinstance(arg, Expr) else arg for arg in eq.args])


def polarify(eq, subs=True, lift=False):
    """
    Turn all numbers in eq into their polar equivalents (under the standard
    choice of argument).

    Note that no attempt is made to guess a formal convention of adding
    polar numbers, expressions like 1 + x will generally not be altered.

    Note also that this function does not promote exp(x) to exp_polar(x).

    If ``subs`` is True, all symbols which are not already polar will be
    substituted for polar dummies; in this case the function behaves much
    like posify.

    If ``lift`` is True, both addition statements and non-polar symbols are
    changed to their polar_lift()ed versions.
    Note that lift=True implies subs=False.

    >>> from sympy import polarify, sin, I
    >>> from sympy.abc import x, y
    >>> expr = (-x)**y
    >>> expr.expand()
    (-x)**y
    >>> polarify(expr)
    ((_x*exp_polar(I*pi))**_y, {_x: x, _y: y})
    >>> polarify(expr)[0].expand()
    _x**_y*exp_polar(_y*I*pi)
    >>> polarify(x, lift=True)
    polar_lift(x)
    >>> polarify(x*(1+y), lift=True)
    polar_lift(x)*polar_lift(y + 1)

    Adds are treated carefully:

    >>> polarify(1 + sin((1 + I)*x))
    (sin(_x*polar_lift(1 + I)) + 1, {_x: x})
    """
    if lift:
        subs = False
    eq = _polarify(sympify(eq), lift)
    if not subs:
        return eq
    reps = {s: Dummy(s.name, polar=True) for s in eq.free_symbols}
    eq = eq.subs(reps)
    return eq, {r: s for s, r in reps.items()}


def _unpolarify(eq, exponents_only, pause=False):
    if not isinstance(eq, Basic) or eq.is_Atom:
        return eq

    if not pause:
        if isinstance(eq, exp_polar):
            return exp(_unpolarify(eq.exp, exponents_only))
        if isinstance(eq, principal_branch) and eq.args[1] == 2 * pi:
            return _unpolarify(eq.args[0], exponents_only)
        if (
            eq.is_Add or eq.is_Mul or eq.is_Boolean or
            eq.is_Relational and (
                eq.rel_op in ('==', '!=') and 0 in eq.args or
                eq.rel_op not in ('==', '!='))
        ):
            return eq.func(*[_unpolarify(x, exponents_only) for x in eq.args])
        if isinstance(eq, polar_lift):
            return _unpolarify(eq.args[0], exponents_only)

    if eq.is_Pow:
        expo = _unpolarify(eq.exp, exponents_only)
        base = _unpolarify(eq.base, exponents_only,
            not (expo.is_integer and not pause))
        return base ** expo

    if eq.is_Function and getattr(eq.func, 'unbranched', False):
        return eq.func(*[_unpolarify(x, exponents_only, exponents_only)
            for x in eq.args])

    return eq.func(*[_unpolarify(x, exponents_only, True) for x in eq.args])


def unpolarify(eq, subs={}, exponents_only=False):
    """
    If p denotes the projection from the Riemann surface of the logarithm to
    the complex line, return a simplified version eq' of `eq` such that
    p(eq') == p(eq).
    Also apply the substitution subs in the end. (This is a convenience, since
    ``unpolarify``, in a certain sense, undoes polarify.)

    >>> from sympy import unpolarify, polar_lift, sin, I
    >>> unpolarify(polar_lift(I + 2))
    2 + I
    >>> unpolarify(sin(polar_lift(I + 7)))
    sin(7 + I)
    """
    if isinstance(eq, bool):
        return eq

    eq = sympify(eq)
    if subs != {}:
        return unpolarify(eq.subs(subs))
    changed = True
    pause = False
    if exponents_only:
        pause = True
    while changed:
        changed = False
        res = _unpolarify(eq, exponents_only, pause)
        if res != eq:
            changed = True
            eq = res
        if isinstance(res, bool):
            return res
    # Finally, replacing Exp(0) by 1 is always correct.
    # So is polar_lift(0) -> 0.
    return res.subs({exp_polar(0): 1, polar_lift(0): 0})


# /cyclic/
from sympy.core import basic as _
_.abs_ = Abs
del _
