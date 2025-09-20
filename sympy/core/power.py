from math import log as _log

from .sympify import _sympify
from .cache import cacheit
from .singleton import S
from .expr import Expr
from .evalf import PrecisionExhausted
from .function import expand_complex, expand_multinomial, expand_mul
from .logic import fuzzy_bool, fuzzy_not, fuzzy_and
from .compatibility import as_int
from .parameters import global_parameters
from sympy.utilities.iterables import sift

from mpmath.libmp import sqrtrem as mpmath_sqrtrem
from math import sqrt as _sqrt

###############################################################################
############################# ROOT and SQUARE ROOT FUNCTION ###################
###############################################################################


def sqrt(arg, evaluate=None):
    """The square root function

    sqrt(x) -> Returns the principal square root of x.

    The parameter evaluate determines if the expression should be evaluated.
    If None, its value is taken from global_evaluate

    Examples
    ========

    >>> from sympy import sqrt, Symbol
    >>> x = Symbol('x')

    >>> sqrt(x)
    sqrt(x)

    >>> sqrt(x)**2
    x

    Note that sqrt(x**2) does not simplify to x.

    >>> sqrt(x**2)
    sqrt(x**2)

    This is because the two are not equal to each other in general.
    For example, consider x == -1:

    >>> from sympy import Eq
    >>> Eq(sqrt(x**2), x).subs(x, -1)
    False

    This is because sqrt computes the principal square root, so the square may
    put the argument in a different branch.  This identity does hold if x is
    positive:

    >>> y = Symbol('y', positive=True)
    >>> sqrt(y**2)
    y

    You can force this simplification by using the powdenest() function with
    the force option set to True:

    >>> from sympy import powdenest
    >>> sqrt(x**2)
    sqrt(x**2)
    >>> powdenest(sqrt(x**2), force=True)
    x

    To get both branches of the square root you can use the rootof function:

    >>> from sympy import rootof

    >>> [rootof(x**2-3,i) for i in (0,1)]
    [-sqrt(3), sqrt(3)]

    See Also
    ========

    sympy.polys.rootoftools.rootof, root, real_root

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Square_root
    .. [2] https://en.wikipedia.org/wiki/Principal_value
    """
    # arg = sympify(arg) is handled by Pow
    return Pow(arg, S.Half, evaluate=evaluate)


def isqrt(n):
    """Return the largest integer less than or equal to sqrt(n)."""
    if n < 17984395633462800708566937239552:
        return int(_sqrt(n))
    return integer_nthroot(int(n), 2)[0]


def integer_nthroot(y, n):
    """
    Return a tuple containing x = floor(y**(1/n))
    and a boolean indicating whether the result is exact (that is,
    whether x**n == y).

    Examples
    ========

    >>> from sympy import integer_nthroot
    >>> integer_nthroot(16, 2)
    (4, True)
    >>> integer_nthroot(26, 2)
    (5, False)

    To simply determine if a number is a perfect square, the is_square
    function should be used:

    >>> from sympy.ntheory.primetest import is_square
    >>> is_square(26)
    False

    See Also
    ========
    sympy.ntheory.primetest.is_square
    integer_log
    """
    y, n = as_int(y), as_int(n)
    if y < 0:
        raise ValueError("y must be nonnegative")
    if n < 1:
        raise ValueError("n must be positive")
    if y in (0, 1):
        return y, True
    if n == 1:
        return y, True
    if n == 2:
        x, rem = mpmath_sqrtrem(y)
        return int(x), not rem
    if n > y:
        return 1, False
    # Get initial estimate for Newton's method. Care must be taken to
    # avoid overflow
    try:
        guess = int(y ** (1. / n) + 0.5)
    except OverflowError:
        exp = _log(y, 2) / n
        if exp > 53:
            shift = int(exp - 53)
            guess = int(2.0 ** (exp - shift) + 1) << shift
        else:
            guess = int(2.0 ** exp)
    if guess > 2 ** 50:
        # Newton iteration
        xprev, x = -1, guess
        while 1:
            t = x ** (n - 1)
            xprev, x = x, ((n - 1) * x + y // t) // n
            if abs(x - xprev) < 2:
                break
    else:
        x = guess
    # Compensate
    t = x ** n
    while t < y:
        x += 1
        t = x ** n
    while t > y:
        x -= 1
        t = x ** n
    return int(x), t == y  # int converts long to int if possible


def integer_log(y, x):
    """Returns (e, bool) where e is the largest nonnegative integer
    such that |y| >= |x**e| and bool is True if y == x**e

    Examples
    ========

    >>> from sympy import integer_log
    >>> integer_log(125, 5)
    (3, True)
    >>> integer_log(17, 9)
    (1, False)
    >>> integer_log(4, -2)
    (2, True)
    >>> integer_log(-125,-5)
    (3, True)

    See Also
    ========
    integer_nthroot
    sympy.ntheory.primetest.is_square
    sympy.ntheory.factor_.multiplicity
    sympy.ntheory.factor_.perfect_power
    """
    if x == 1:
        raise ValueError('x cannot take value as 1')
    if y == 0:
        raise ValueError('y cannot take value as 0')

    if x in (-2, 2):
        x = int(x)
        y = as_int(y)
        e = y.bit_length() - 1
        return e, x ** e == y
    if x < 0:
        n, b = integer_log(y if y > 0 else -y, -x)
        return n, b and bool(n % 2 if y < 0 else not n % 2)

    x = as_int(x)
    y = as_int(y)
    r = e = 0
    while y >= x:
        d = x
        m = 1
        while y >= d:
            y, rem = divmod(y, d)
            r = r or rem
            e += m
            if y > d:
                d *= d
                m *= 2
    return e, r == 0 and y == 1


class Pow(Expr):
    """
    Defines the expression x**y as "x raised to a power y"

    Singleton definitions involving (0, 1, -1, oo, -oo, I, -I):

    +--------------+---------+-----------------------------------------------+
    | expr         | value   | reason                                        |
    +==============+=========+===============================================+
    | z**0         | 1       | Although arguments over 0**0 exist, see [2].  |
    +--------------+---------+-----------------------------------------------+
    | z**1         | z       |                                               |
    +--------------+---------+-----------------------------------------------+
    | (-oo)**(-1)  | 0       |                                               |
    +--------------+---------+-----------------------------------------------+
    | (-1)**-1     | -1      |                                               |
    +--------------+---------+-----------------------------------------------+
    | S.Zero**-1   | zoo     | This is not strictly true, as 0**-1 may be    |
    |              |         | undefined, but is convenient in some contexts |
    |              |         | where the base is assumed to be positive.     |
    +--------------+---------+-----------------------------------------------+
    | 1**-1        | 1       |                                               |
    +--------------+---------+-----------------------------------------------+
    | oo**-1       | 0       |                                               |
    +--------------+---------+-----------------------------------------------+
    | 0**oo        | 0       | Because for all complex numbers z near        |
    |              |         | 0, z**oo -> 0.                                |
    +--------------+---------+-----------------------------------------------+
    | 0**-oo       | zoo     | This is not strictly true, as 0**oo may be    |
    |              |         | oscillating between positive and negative     |
    |              |         | values or rotating in the complex plane.      |
    |              |         | It is convenient, however, when the base      |
    |              |         | is positive.                                  |
    +--------------+---------+-----------------------------------------------+
    | 1**oo        | nan     | Because there are various cases where         |
    | 1**-oo       |         | lim(x(t),t)=1, lim(y(t),t)=oo (or -oo),       |
    |              |         | but lim( x(t)**y(t), t) != 1.  See [3].       |
    +--------------+---------+-----------------------------------------------+
    | b**zoo       | nan     | Because b**z has no limit as z -> zoo         |
    +--------------+---------+-----------------------------------------------+
    | (-1)**oo     | nan     | Because of oscillations in the limit.         |
    | (-1)**(-oo)  |         |                                               |
    +--------------+---------+-----------------------------------------------+
    | oo**oo       | oo      |                                               |
    +--------------+---------+-----------------------------------------------+
    | oo**-oo      | 0       |                                               |
    +--------------+---------+-----------------------------------------------+
    | (-oo)**oo    | nan     |                                               |
    | (-oo)**-oo   |         |                                               |
    +--------------+---------+-----------------------------------------------+
    | oo**I        | nan     | oo**e could probably be best thought of as    |
    | (-oo)**I     |         | the limit of x**e for real x as x tends to    |
    |              |         | oo. If e is I, then the limit does not exist  |
    |              |         | and nan is used to indicate that.             |
    +--------------+---------+-----------------------------------------------+
    | oo**(1+I)    | zoo     | If the real part of e is positive, then the   |
    | (-oo)**(1+I) |         | limit of abs(x**e) is oo. So the limit value  |
    |              |         | is zoo.                                       |
    +--------------+---------+-----------------------------------------------+
    | oo**(-1+I)   | 0       | If the real part of e is negative, then the   |
    | -oo**(-1+I)  |         | limit is 0.                                   |
    +--------------+---------+-----------------------------------------------+

    Because symbolic computations are more flexible that floating point
    calculations and we prefer to never return an incorrect answer,
    we choose not to conform to all IEEE 754 conventions.  This helps
    us avoid extra test-case code in the calculation of limits.

    See Also
    ========

    sympy.core.numbers.Infinity
    sympy.core.numbers.NegativeInfinity
    sympy.core.numbers.NaN

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Exponentiation
    .. [2] https://en.wikipedia.org/wiki/Exponentiation#Zero_to_the_power_of_zero
    .. [3] https://en.wikipedia.org/wiki/Indeterminate_forms

    """

    __slots__ = ['is_commutative']

    @cacheit
    def _eval_shape(self):
        b, e = self.args
        if e.shape:
            if b.shape:
                assert b.shape == e.shape
            return e.shape
        return b.shape
    
    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        if self.exp.is_integer:
            if self.exp.is_negative:
                if self.base.is_rational:
                    if self.base.is_nonnegative:
                        return dtype.rational(positive=True)                    
                    return dtype.rational
                return  dtype.real
            return self.base.dtype
        return dtype.real

    @cacheit
    def __new__(cls, b, e, evaluate=None):
        if evaluate is None:
            evaluate = global_parameters.evaluate
        from sympy.functions.elementary.exponential import exp_polar

        b = _sympify(b)
        e = _sympify(e)
        if evaluate:
            if e is S.ComplexInfinity:
                return S.NaN
            if e is S.Zero:
                from sympy import Ones
                return Ones(*b.shape)
            elif e is S.One:
                return b
            elif e == -1 and not b:
                return S.ComplexInfinity
            # Only perform autosimplification if exponent or base is a Symbol or number
            elif (b.is_Symbol or b.is_number) and (e.is_Symbol or e.is_number) and\
                e.is_integer and b._coeff_isneg():
                if e.is_even:
                    b = -b
                elif e.is_odd:
                    return -Pow(-b, e)
            if S.NaN in (b, e):  # XXX S.NaN**x -> S.NaN under assumption that x != 0
                return S.NaN
            elif b is S.One:
                if abs(e).is_infinite:
                    return S.NaN
                return S.One
            else:
                # recognize base as E
                if not e.is_Atom and b is not S.Exp1 and not isinstance(b, exp_polar):
                    from sympy import numer, denom, log, sign, Im, factor_terms
                    c, ex = factor_terms(e, sign=False).as_coeff_Mul()
                    den = denom(ex)
                    if isinstance(den, log) and den.args[0] == b:
                        return S.Exp1 ** (c * numer(ex))
                    elif den.is_Add:
                        s = sign(Im(b))
                        if s.is_Number and s and den == \
                                log(-factor_terms(b, sign=False)) + s * S.ImaginaryUnit * S.Pi:
                            return S.Exp1 ** (c * numer(ex))

                try:
                    obj = b._eval_power(e)
                except (AttributeError, TypeError):
                    from sympy import sympify, Basic
                    if isinstance(e, int):
                        e = sympify(e)
                    return Basic.__new__(Pow, b, e)
                
                if obj is not None:
                    return obj
        obj = Expr.__new__(cls, b, e)
        obj = cls._exec_constructor_postprocessors(obj)
        if not isinstance(obj, Pow):
            return obj
#         obj.is_commutative = (b.is_commutative and e.is_commutative)
        return obj

    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices):
        base, exp = self.args
        if base.shape:
            base = base[indices]
            
        if exp.shape:
            exp = exp[indices]                
            
        return self.func(base, exp, evaluate=base.is_Number)
    
    @property
    def base(self):
        return self._args[0]

    @property
    def exp(self):
        return self._args[1]

    @classmethod
    def class_key(cls):
        return 3, 2, cls.__name__

    def _eval_refine(self, assumptions):
        from sympy.assumptions.ask import ask, Q
        b, e = self.as_base_exp()
        if ask(Q.integer(e), assumptions) and b._coeff_isneg():
            if ask(Q.even(e), assumptions):
                return Pow(-b, e)
            elif ask(Q.odd(e), assumptions):
                return -Pow(-b, e)

    def _eval_power(self, other):
        from sympy import arg, exp, floor, Im, log, Re, sign
        b, e = self.as_base_exp()
        if b is S.NaN:
            return (b ** e) ** other  # let __new__ handle it

        s = None
        if other.is_integer:
            if b.is_NegativeOne and other.is_odd:
                return self
            s = 1
        elif b.is_polar:  # e.g. exp_polar, besselj, var('p', polar=True)...
            s = 1
        elif e.is_extended_real is not None:

            # helper functions ===========================
            def _half(e):
                """Return True if the exponent has a literal 2 as the
                denominator, else None."""
                if getattr(e, 'q', None) == 2:
                    return True
                n, d = e.as_numer_denom()
                if n.is_integer and d == 2:
                    return True

            def _n2(e):
                """Return ``e`` evaluated to a Number with 2 significant
                digits, else None."""
                try:
                    rv = e.evalf(2, strict=True)
                    if rv.is_Number:
                        return rv
                except PrecisionExhausted:
                    pass

            # ===================================================
            if e.is_extended_real:
                # we need _half(other) with constant floor or
                # floor(S.Half - e*arg(b)/2/pi) == 0

                # handle -1 as special case
                if e == -1:
                    # floor arg. is 1/2 + arg(b)/2/pi
                    if _half(other):
                        if b.is_negative == True:
                            return S.NegativeOne ** other * Pow(-b, e * other)
                        if b.is_extended_real == False or other == S.One / 2:
                            return Pow(b, -other)
                elif e.is_even:
                    if b.is_extended_real:
                        b = abs(b)
                    if b.is_imaginary:
                        b = abs(Im(b)) * S.ImaginaryUnit

                if (abs(e) < 1) == True or e == 1:
                    s = 1  # floor = 0
                elif b.is_extended_nonnegative:
                    s = 1  # floor = 0
                elif Re(b).is_extended_nonnegative and (abs(e) < 2) == True:
                    s = 1  # floor = 0
                elif fuzzy_not(Im(b).is_zero) and abs(e) == 2:
                    s = 1  # floor = 0
                elif _half(other):
                    s = exp(2 * S.Pi * S.ImaginaryUnit * other * floor(
                        S.Half - e * arg(b) / (2 * S.Pi)))
                    if s.is_extended_real and _n2(sign(s) - s) == 0:
                        s = sign(s)
                    else:
                        s = None
            else:
                # e.is_extended_real == False requires:
                #     _half(other) with constant floor or
                #     floor(S.Half - im(e*log(b))/2/pi) == 0
                try:
                    s = exp(2 * S.ImaginaryUnit * S.Pi * other * 
                        floor(S.Half - Im(e * log(b)) / 2 / S.Pi))
                    # be careful to test that s is -1 or 1 b/c sign(I) == I:
                    # so check that s is real
                    if s.is_extended_real and _n2(sign(s) - s) == 0:
                        s = sign(s)
                    else:
                        s = None
                except PrecisionExhausted:
                    s = None

        if s is not None:
            return s * Pow(b, e * other)

    def _eval_Mod(self, q):
        if self.exp.is_integer and self.exp.is_positive:
            if q.is_integer and self.base % q == 0:
                return S.Zero

            '''
            For unevaluated Integer power, use built-in pow modular
            exponentiation, if powers are not too large wrt base.
            '''
            if self.base.is_Integer and self.exp.is_Integer and q.is_Integer:
                b, e, m = int(self.base), int(self.exp), int(q)
                # For very large powers, use totient reduction if e >= lg(m).
                # Bound on m, is for safe factorization memory wise ie m^(1/4).
                # For pollard-rho to be faster than built-in pow lg(e) > m^(1/4)
                # check is added.
                mb = m.bit_length()
                if mb <= 80  and e >= mb and e.bit_length() ** 4 >= m:
                    from sympy.ntheory import totient
                    phi = totient(m)
                    return pow(b, phi + e % phi, m)
                else:
                    return pow(b, e, m)

    def _eval_is_even(self):
        if self.exp.is_integer:
            if self.exp.is_positive:
                return self.base.is_even
            if self.exp.is_nonnegative and self.base.is_odd:
                return False
            if self.base is S.NegativeOne:
                return False

    def _eval_is_extended_positive(self):
        from sympy import log
        if self.base == self.exp:
            if self.base.is_extended_nonnegative:
                return True
        elif self.base.is_extended_positive:
            if self.exp.is_extended_real:
                return True
        elif self.base.is_extended_negative:
            if self.exp.is_even:
                return True
            if self.exp.is_odd:
                return False
        elif self.base.is_zero:
            if self.exp.is_extended_real:
                return self.exp.is_zero
        elif self.base.is_extended_nonpositive:
            if self.exp.is_odd:
                return False
        elif self.base.is_extended_nonnegative:
            if self.exp.is_extended_negative:
                return True
        elif self.base.is_imaginary:
            if self.exp.is_integer:
                m = self.exp % 4
                if m.is_zero:
                    return True
                if m.is_integer and m.is_zero == False:
                    return False
            if self.exp.is_imaginary:
                return log(self.base).is_imaginary

    def _eval_is_extended_negative(self):
        if self.base.is_extended_negative:
            if self.exp.is_odd and self.base.is_finite:
                return True
            if self.exp.is_even:
                return False
        elif self.base.is_extended_positive:
            if self.exp.is_extended_real:
                return False
        elif self.base.is_zero:
            if self.exp.is_extended_real:
                return False
        elif self.base.is_extended_nonnegative:
            if self.exp.is_extended_nonnegative:
                return False
        elif self.base.is_extended_nonpositive:
            if self.exp.is_even:
                return False
        elif self.base.is_extended_real:
            if self.exp.is_even:
                return False

    def _eval_is_zero(self):
        if self.base.is_zero:
            if self.exp.is_extended_positive:
                return True
            elif self.exp.is_extended_nonpositive:
                return False
        elif self.base.is_zero == False:
            if self.exp.is_negative:
                return self.base.is_infinite
            elif self.exp.is_nonnegative:
                return False
            elif self.exp.is_infinite:
                if (1 - abs(self.base)).is_extended_positive:
                    return self.exp.is_extended_positive
                elif (1 - abs(self.base)).is_extended_negative:
                    return self.exp.is_extended_negative
            if self.base.is_extended_positive or self.base.is_NegativeOne or self.exp.is_integer:
                return False
        else:
            if self.base.is_nonzero:
                return False
            if self.exp.is_extended_negative:
                return False

    def _eval_is_extended_integer(self):
        b, e = self.args
        if b.is_extended_rational:
            if b.is_extended_integer == False and e.is_extended_positive:
                return False
        if b.is_extended_integer and e.is_extended_integer:
            if b.is_NegativeOne:
                return True
            if e.is_extended_nonnegative or e.is_extended_positive:
                return True
        if b.is_extended_integer and e.is_extended_negative and (e.is_finite or e.is_extended_integer):
            if fuzzy_not((b - 1).is_zero) and fuzzy_not((b + 1).is_zero):
                return False
        if b.is_Number and e.is_Number:
            check = self.func(*self.args)
            return check.is_Integer

    def _eval_is_super_integer(self):
        b, e = self.args
        if e.is_extended_integer and e.is_extended_positive:
            return b.is_super_integer

    def _eval_is_extended_rational(self):
        b, e = self.args
        if b.is_extended_rational:
            if e.is_extended_integer:
                return True
        
    def _eval_is_hyper_rational(self):
        b, e = self.args
        if e.is_integer:
            return b.is_hyper_rational
        
    def _eval_is_super_rational(self):
        b, e = self.args
        if e.is_integer:
            return b.is_super_rational
        
    def _eval_is_extended_real(self):
        from sympy import arg, exp, log, Mul
        real_b = self.base.is_extended_real
        if real_b is None:
            if self.base.func == exp and self.base.args[0].is_imaginary:
                return self.exp.is_imaginary
            return
        real_e = self.exp.is_extended_real
        if real_e is None:
            return
        if real_b and real_e:
            if self.base.is_extended_positive:
                return True
            elif self.base.is_extended_nonnegative:
                if self.exp.is_extended_nonnegative:
                    return True
            else:
                if self.exp.is_integer:
                    return True
                elif self.base.is_extended_negative:
                    if self.exp.is_Rational:
                        return False
        if real_e and self.exp.is_extended_negative:
            return Pow(self.base, -self.exp).is_extended_real
        im_b = self.base.is_imaginary
        im_e = self.exp.is_imaginary
        if im_b:
            if self.exp.is_integer:
                if self.exp.is_even:
                    return True
                elif self.exp.is_odd:
                    return False
            elif im_e and log(self.base).is_imaginary:
                return True
            elif self.exp.is_Add:
                c, a = self.exp.as_coeff_Add()
                if c and c.is_Integer:
                    return Mul(
                        self.base ** c, self.base ** a, evaluate=False).is_extended_real
            elif self.base in (-S.ImaginaryUnit, S.ImaginaryUnit):
                if (self.exp / 2).is_integer == False:
                    return False
        if real_b and im_e:
            if self.base is S.NegativeOne:
                return True
            c = self.exp.coeff(S.ImaginaryUnit)
            if c:
                ok = (c * log(self.base) / S.Pi).is_Integer
                if ok is not None:
                    return ok

        if real_b is False:  # we already know it's not imag
            i = arg(self.base) * self.exp / S.Pi
            return i.is_integer
    
    def _eval_is_hyper_real(self):
        b, e = self.args
        if e.is_integer:
            return b.is_hyper_real
        
    def _eval_is_super_real(self):
        b, e = self.args
        if e.is_integer:
            return b.is_super_real
    
    def _eval_is_extended_complex(self):
        b, e = self.args
        return b.is_extended_complex and e.is_extended_complex

    def _eval_is_imaginary(self):
        from sympy import arg, log
        if self.base.is_imaginary:
            if self.exp.is_integer:
                odd = self.exp.is_odd
                if odd is not None:
                    return odd
                return

        if self.exp.is_imaginary:
            imlog = log(self.base).is_imaginary
            if imlog is not None:
                return False  # I**i -> real; (2*I)**i -> complex ==> not imaginary

        if self.base.is_extended_real and self.exp.is_extended_real:
            if self.base.is_positive:
                return False
            else:
                rat = self.exp.is_rational
                if not rat:
                    return rat
                if self.exp.is_integer:
                    return False
                else:
                    half = (2 * self.exp).is_integer
                    if half:
                        return self.base.is_negative
                    return half

        if self.base.is_extended_real == False:  # we already know it's not imag
            i = arg(self.base) * self.exp / S.Pi
            isodd = (2 * i).is_odd
            if isodd is not None:
                return isodd

        if self.exp.is_negative:
            return (1 / self).is_imaginary

    def _eval_is_finite(self):
        if self.exp.is_negative:
            if self.base.is_zero:
                return False
            if self.base.is_infinite or self.base.is_nonzero:
                return True
            if self.base.is_finite:
                return True
            
        c1 = self.base.is_finite
        if c1 is None:
            return
        c2 = self.exp.is_finite
        if c2 is None:
            return
        if c1 and c2:
            if self.exp.is_nonnegative or fuzzy_not(self.base.is_zero):
                return True

    def _eval_is_prime(self):
        '''
        An integer raised to the n(>=2)-th power cannot be a prime.
        '''
        if self.base.is_integer and self.exp.is_integer and (self.exp - 1).is_positive:
            return False

    def _eval_is_composite(self):
        """
        A power is composite if both base and exponent are greater than 1
        """
        if (self.base.is_integer and self.exp.is_integer and
            ((self.base - 1).is_positive and (self.exp - 1).is_positive or
            (self.base + 1).is_negative and self.exp.is_positive and self.exp.is_even)):
            return True

    def _eval_is_polar(self):
        return self.base.is_polar

    def _eval_subs(self, old, new, **hints):
        from sympy import exp, log, Symbol

        def _check(ct1, ct2, old):
            """Return (bool, pow, remainder_pow) where, if bool is True, then the
            exponent of Pow `old` will combine with `pow` so the substitution
            is valid, otherwise bool will be False.

            For noncommutative objects, `pow` will be an integer, and a factor
            `Pow(old.base, remainder_pow)` needs to be included. If there is
            no such factor, None is returned. For commutative objects,
            remainder_pow is always None.

            cti are the coefficient and terms of an exponent of self or old
            In this _eval_subs routine a change like (b**(2*x)).subs(b**x, y)
            will give y**2 since (b**x)**2 == b**(2*x); if that equality does
            not hold then the substitution should not occur so `bool` will be
            False.

            """
            coeff1, terms1 = ct1
            coeff2, terms2 = ct2
            if terms1 == terms2:
                # Allow fractional powers for commutative objects
                pow = coeff1 / coeff2
                try:
                    as_int(pow, strict=False)
                    combines = True
                except ValueError:
                    combines = isinstance(Pow._eval_power(
                        Pow(*old.as_base_exp(), evaluate=False),
                        pow), (Pow, exp, Symbol))
                return combines, pow, None

            return False, None, None

        if old == self.base:
            return new ** self.exp._subs(old, new)

        # issue 10829: (4**x - 3*y + 2).subs(2**x, y) -> y**2 - 3*y + 2
        if isinstance(old, self.func) and self.exp == old.exp:
            l = log(self.base, old.base)
            if l.is_Number:
                return Pow(new, l)

        if isinstance(old, self.func) and self.base == old.base:
            if self.exp.is_Add is False:
                ct1 = self.exp.as_independent(Symbol, as_Add=False)
                ct2 = old.exp.as_independent(Symbol, as_Add=False)
                ok, pow, remainder_pow = _check(ct1, ct2, old)
                if ok:
                    # issue 5180: (x**(6*y)).subs(x**(3*y),z)->z**2
                    result = self.func(new, pow)
                    if remainder_pow is not None:
                        result = Mul(result, Pow(old.base, remainder_pow))
                    return result
            else:  # b**(6*x + a).subs(b**(3*x), y) -> y**2 * b**a
                # exp(exp(x) + exp(x**2)).subs(exp(exp(x)), w) -> w * exp(exp(x**2))
                oarg = old.exp
                new_l = []
                o_al = []
                ct2 = oarg.as_coeff_mul()
                for a in self.exp.args:
                    newa = a._subs(old, new)
                    ct1 = newa.as_coeff_mul()
                    ok, pow, remainder_pow = _check(ct1, ct2, old)
                    if ok:
                        new_l.append(new ** pow)
                        if remainder_pow is not None:
                            o_al.append(remainder_pow)
                        continue
                    o_al.append(newa)
                if new_l:
                    expo = Add(*o_al)
                    new_l.append(Pow(self.base, expo, evaluate=False) if expo != 1 else self.base)
                    return Mul(*new_l)

        if isinstance(old, exp) and self.exp.is_extended_real and self.base.is_positive:
            ct1 = old.args[0].as_independent(Symbol, as_Add=False)
            ct2 = (self.exp * log(self.base)).as_independent(
                Symbol, as_Add=False)
            ok, pow, remainder_pow = _check(ct1, ct2, old)
            if ok:
                result = self.func(new, pow)  # (2**x).subs(exp(x*log(2)), z) -> z
                if remainder_pow is not None:
                    result = Mul(result, Pow(old.base, remainder_pow))
                return result

    def as_base_exp(self):
        """Return base and exp of self.

        If base is 1/Integer, then return Integer, -exp. If this extra
        processing is not needed, the base and exp properties will
        give the raw arguments

        Examples
        ========

        >>> from sympy import Pow, S
        >>> p = Pow(S.Half, 2, evaluate=False)
        >>> p.as_base_exp()
        (2, -2)
        >>> p.args
        (1/2, 2)

        """

        b, e = self.args
        if b.is_Rational and b.p == 1 and b.q != 1:
            return Integer(b.q), -e
        return b, e

    def _eval_adjoint(self):
        from sympy import Adjoint
        i, p = self.exp.is_integer, self.base.is_positive
        if i:
            return Adjoint(self.base) ** self.exp
        if p:
            return self.base ** Adjoint(self.exp)
        if i is False and p is False:
            expanded = expand_complex(self)
            if expanded != self:
                return Adjoint(expanded)

    def _eval_conjugate(self):
        from sympy.functions.elementary.complexes import conjugate as c
        i, p = self.exp.is_integer, self.base.is_positive
        if i:
            return c(self.base) ** self.exp
        if p:
            return self.base ** c(self.exp)
        if i is False and p is False:
            expanded = expand_complex(self)
            if expanded != self:
                return c(expanded)
        if self.is_extended_real:
            return self

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            i, p = self.exp.is_integer, self.base.is_complex
            if p:
                return self.base.T ** self.exp
            if i:
                return self.base.T ** self.exp
            if i is False and p is False:
                expanded = expand_complex(self)
                if expanded != self:
                    return expanded.T

    def _eval_expand_power_exp(self, **hints):
        """a**(n + m) -> a**n*a**m"""
        b = self.base
        e = self.exp
#         if e.is_Add and e.is_commutative:
        if e.is_Add:
            expr = []
            for x in e.args:
                expr.append(self.func(self.base, x))
            return Mul(*expr)
        return self.func(b, e)

    def _eval_expand_power_base(self, **hints):
        """(a*b)**n -> a**n * b**n"""
        force = hints.get('force', False)

        b = self.base
        e = self.exp
        if not b.is_Mul:
            return self

        cargs, nc = b.args_cnc(split_1=False)

        # expand each term - this is top-level-only
        # expansion but we have to watch out for things
        # that don't have an _eval_expand method
        if nc:
            nc = [i._eval_expand_power_base(**hints)
                if hasattr(i, '_eval_expand_power_base') else i
                for i in nc]

            if e.is_Integer:
                if e.is_positive:
                    rv = Mul(*nc * e)
                else:
                    rv = Mul(*[i ** -1 for i in nc[::-1]] * -e)
                if cargs:
                    rv *= Mul(*cargs) ** e
                return rv

            if not cargs:
                return self.func(Mul(*nc), e, evaluate=False)

            nc = [Mul(*nc)]

        # sift the commutative bases
        other, maybe_real = sift(cargs, lambda x: x.is_extended_real == False,
            binary=True)

        def pred(x):
            if x is S.ImaginaryUnit:
                return S.ImaginaryUnit
            polar = x.is_polar
            if polar:
                return True
            if polar is None:
                return fuzzy_bool(x.is_extended_nonnegative)

        sifted = sift(maybe_real, pred)
        nonneg = sifted[True]
        other += sifted[None]
        neg = sifted[False]
        imag = sifted[S.ImaginaryUnit]
        if imag:
            I = S.ImaginaryUnit
            i = len(imag) % 4
            if i == 0:
                pass
            elif i == 1:
                other.append(I)
            elif i == 2:
                if neg:
                    nonn = -neg.pop()
                    if nonn is not S.One:
                        nonneg.append(nonn)
                else:
                    neg.append(S.NegativeOne)
            else:
                if neg:
                    nonn = -neg.pop()
                    if nonn is not S.One:
                        nonneg.append(nonn)
                else:
                    neg.append(S.NegativeOne)
                other.append(I)
            del imag

        # bring out the bases that can be separated from the base

        if force or e.is_integer:
            # treat all commutatives the same and put nc in other
            cargs = nonneg + neg + other
            other = nc
        else:
            # this is just like what is happening automatically, except
            # that now we are doing it for an arbitrary exponent for which
            # no automatic expansion is done

            assert not e.is_Integer

            # handle negatives by making them all positive and putting
            # the residual -1 in other
            if len(neg) > 1:
                o = S.One
                if not other and neg[0].is_Number:
                    o *= neg.pop(0)
                if len(neg) % 2:
                    o = -o
                for n in neg:
                    nonneg.append(-n)
                if o is not S.One:
                    other.append(o)
            elif neg and other:
                if neg[0].is_Number and neg[0] is not S.NegativeOne:
                    other.append(S.NegativeOne)
                    nonneg.append(-neg[0])
                else:
                    other.extend(neg)
            else:
                other.extend(neg)
            del neg

            cargs = nonneg
            other += nc

        rv = S.One
        if cargs:
            if e.is_Rational:
                npow, cargs = sift(cargs, lambda x: x.is_Pow and
                    x.exp.is_Rational and x.base.is_number,
                    binary=True)
                rv = Mul(*[self.func(b.func(*b.args), e) for b in npow])
            rv *= Mul(*[self.func(b, e, evaluate=True) for b in cargs])
        if other:
            rv *= self.func(Mul(*other), e, evaluate=cargs)
        return rv

    def _eval_expand_multinomial(self, **hints):
        """(a + b + ..)**n -> a**n + n*a**(n-1)*b + .., n is nonzero integer"""

        base, exp = self.args
        result = self

        if exp.is_Rational and exp.p > 0 and base.is_Add:
            if not exp.is_Integer:
                n = Integer(exp.p // exp.q)

                if not n:
                    return result
                else:
                    radical, result = self.func(base, exp - n), []

                    expanded_base_n = self.func(base, n)
                    if expanded_base_n.is_Pow:
                        expanded_base_n = \
                            expanded_base_n._eval_expand_multinomial()
                    for term in Add.make_args(expanded_base_n):
                        result.append(term * radical)

                    return Add(*result)

            n = int(exp)

#             if base.is_commutative:
            order_terms, other_terms = [], []

            for b in base.args:
                if b.is_Order:
                    order_terms.append(b)
                else:
                    other_terms.append(b)

            if order_terms:
                # (f(x) + O(x^n))^m -> f(x)^m + m*f(x)^{m-1} *O(x^n)
                f = Add(*other_terms)
                o = Add(*order_terms)

                if n == 2:
                    return expand_multinomial(f ** n, deep=False) + n * f * o
                else:
                    g = expand_multinomial(f ** (n - 1), deep=False)
                    return expand_mul(f * g, deep=False) + n * g * o

            if base.is_number:
                # Efficiently expand expressions of the form (a + b*I)**n
                # where 'a' and 'b' are real numbers and 'n' is integer.
                a, b = base.as_real_imag()

                if a.is_Rational and b.is_Rational:
                    if not a.is_Integer:
                        if not b.is_Integer:
                            k = self.func(a.q * b.q, n)
                            a, b = a.p * b.q, a.q * b.p
                        else:
                            k = self.func(a.q, n)
                            a, b = a.p, a.q * b
                    elif not b.is_Integer:
                        k = self.func(b.q, n)
                        a, b = a * b.q, b.p
                    else:
                        k = 1

                    a, b, c, d = int(a), int(b), 1, 0

                    while n:
                        if n & 1:
                            c, d = a * c - b * d, b * c + a * d
                            n -= 1
                        a, b = a * a - b * b, 2 * a * b
                        n //= 2

                    I = S.ImaginaryUnit

                    if k == 1:
                        return c + I * d
                    else:
                        return Integer(c) / k + I * d / k

            p = other_terms
            # (x + y)**3 -> x**3 + 3*x**2*y + 3*x*y**2 + y**3
            # in this particular example:
            # p = [x,y]; n = 3
            # so now it's easy to get the correct result -- we get the
            # coefficients first:
            from sympy import multinomial_coefficients
            from sympy.polys.polyutils import basic_from_dict
            expansion_dict = multinomial_coefficients(len(p), n)
            # in our example: {(3, 0): 1, (1, 2): 3, (0, 3): 1, (2, 1): 3}
            # and now construct the expression.
            return basic_from_dict(expansion_dict, *p)
#             else:
#                 if n == 2:
#                     return Add(*[f * g for f in base.args for g in base.args])
#                 else:
#                     multi = (base ** (n - 1))._eval_expand_multinomial()
#                     if multi.is_Add:
#                         return Add(*[f * g for f in base.args
#                             for g in multi.args])
#                     else:
#                         # XXX can this ever happen if base was an Add?
#                         return Add(*[f * multi for f in base.args])
        elif (exp.is_Rational and exp.p < 0 and base.is_Add and
                abs(exp.p) > exp.q):
            return 1 / self.func(base, -exp)._eval_expand_multinomial()
        elif exp.is_Add and base.is_Number:
            #  a + b      a  b
            # n      --> n  n  , where n, a, b are Numbers

            coeff, tail = S.One, S.Zero
            for term in exp.args:
                if term.is_Number:
                    coeff *= self.func(base, term)
                else:
                    tail += term

            return coeff * self.func(base, tail)
        else:
            return result

    def as_real_imag(self, deep=True, **hints):
        from sympy import atan2, cos, sin
        from sympy.polys.polytools import poly

        if self.exp.is_Integer:
            exp = self.exp
            re, im = self.base.as_real_imag(deep=deep)
            if not im:
                return self, S.Zero
            a, b = symbols('a b', cls=Dummy)
            if exp >= 0:
                if re.is_Number and im.is_Number:
                    # We can be more efficient in this case
                    expr = expand_multinomial(self.base ** exp)
                    if expr != self:
                        return expr.as_real_imag()

                expr = poly(
                    (a + b) ** exp)  # a = re, b = im; expr = (a + b*I)**exp
            else:
                mag = re ** 2 + im ** 2
                re, im = re / mag, -im / mag
                if re.is_Number and im.is_Number:
                    # We can be more efficient in this case
                    expr = expand_multinomial((re + im * S.ImaginaryUnit) ** -exp)
                    if expr != self:
                        return expr.as_real_imag()

                expr = poly((a + b) ** -exp)

            # Terms with even b powers will be real
            r = [i for i in expr.terms() if not i[0][1] % 2]
            re_part = Add(*[cc * a ** aa * b ** bb for (aa, bb), cc in r])
            # Terms with odd b powers will be imaginary
            r = [i for i in expr.terms() if i[0][1] % 4 == 1]
            im_part1 = Add(*[cc * a ** aa * b ** bb for (aa, bb), cc in r])
            r = [i for i in expr.terms() if i[0][1] % 4 == 3]
            im_part3 = Add(*[cc * a ** aa * b ** bb for (aa, bb), cc in r])

            return (re_part.subs({a: re, b: S.ImaginaryUnit * im}),
            im_part1.subs({a: re, b: im}) + im_part3.subs({a: re, b:-im}))

        elif self.exp.is_Rational:
            re, im = self.base.as_real_imag(deep=deep)

            if im.is_zero and self.exp is S.Half:
                if re.is_extended_nonnegative:
                    return self, S.Zero
                if re.is_extended_nonpositive:
                    return S.Zero, (-self.base) ** self.exp

            # XXX: This is not totally correct since for x**(p/q) with
            #      x being imaginary there are actually q roots, but
            #      only a single one is returned from here.
            r = self.func(self.func(re, 2) + self.func(im, 2), S.Half)
            t = atan2(im, re)

            rp, tp = self.func(r, self.exp), t * self.exp

            return (rp * cos(tp), rp * sin(tp))
        else:
            from sympy import Im, Re
            if deep:
                hints['complex'] = False

                expanded = self.expand(deep, **hints)
                if hints.get('ignore') == expanded:
                    return None
                else:
                    return (Re(expanded), Im(expanded))
            else:
                return (Re(self), Im(self))

    def _eval_derivative(self, s):
        from sympy import log
        base, exp = self.args
        if s.shape:
            if exp.shape:
                dbase = base.diff(s)
                dexp = exp.diff(s)
                return self * (dexp * log(base) + dbase * exp / base)
            elif base.shape:
                dbase = base.diff(s)
                dexp = exp.diff(s)
                if len(self.shape) < len(dbase.shape):
                    from sympy import Transpose
                    self = Transpose.expand_dims(self, dbase.shape, len(s.shape))
                    base = Transpose.expand_dims(base, dbase.shape, len(s.shape))

                return self * (dexp * log(base) + dbase * exp / base)
            else:
                dbase = base.diff(s)
                dexp = exp.diff(s)
                return self * (dexp * log(base) + dbase * exp / base)
                
        else:
            dbase = base.diff(s)
            dexp = exp.diff(s)
            return self * (dexp * log(base) + dbase * exp / base)

    def _eval_evalf(self, prec):
        base, exp = self.as_base_exp()
        base = base._evalf(prec)
        if not exp.is_Integer:
            exp = exp._evalf(prec)
        if exp.is_negative and base.is_number and base.is_extended_real == False:
            base = base.conjugate() / (base * base.conjugate())._evalf(prec)
            exp = -exp
            return self.func(base, exp).expand()
        return self.func(base, exp)

    def _eval_is_polynomial(self, syms):
        if self.exp.has(*syms):
            return False

        if self.base.has(*syms):
            return bool(self.base._eval_is_polynomial(syms) and
                self.exp.is_Integer and (self.exp >= 0))
        else:
            return True

    def _eval_is_rational(self):
        # The evaluation of self.func below can be very expensive in the case
        # of integer**integer if the exponent is large.  We should try to exit
        # before that if possible:
        if (self.exp.is_integer and self.base.is_rational
                and fuzzy_not(fuzzy_and([self.exp.is_negative, self.base.is_zero]))):
            return True
        p = self.func(*self.as_base_exp())  # in case it's unevaluated
        if not p.is_Pow:
            return p.is_rational
        b, e = p.as_base_exp()
        if e.is_Rational and b.is_Rational:
            # we didn't check that e is not an Integer
            # because Rational**Integer autosimplifies
            return False
        if e.is_integer:
            if b.is_rational:
                if fuzzy_not(b.is_zero) or e.is_nonnegative:
                    return True
                if b == e:  # always rational, even for 0**0
                    return True
            elif b.is_irrational:
                return e.is_zero

    def _eval_is_algebraic(self):

        def _is_one(expr):
            try:
                return (expr - 1).is_zero
            except ValueError:
                # when the operation is not allowed
                return False

        if self.base.is_zero or _is_one(self.base):
            return True
        elif self.exp.is_rational:
            if self.base.is_algebraic == False:
                return self.exp.is_zero
            return self.base.is_algebraic
        elif self.base.is_algebraic and self.exp.is_algebraic:
            if ((fuzzy_not(self.base.is_zero)
                and fuzzy_not(_is_one(self.base)))
                or self.base.is_integer == False
                or self.base.is_irrational):
                return self.exp.is_rational

    def _eval_is_rational_function(self, syms):
        if self.exp.has(*syms):
            return False

        if self.base.has(*syms):
            return self.base._eval_is_rational_function(syms) and \
                self.exp.is_Integer
        else:
            return True

    def _eval_is_algebraic_expr(self, syms):
        if self.exp.has(*syms):
            return False

        if self.base.has(*syms):
            return self.base._eval_is_algebraic_expr(syms) and \
                self.exp.is_Rational
        else:
            return True

    def _eval_rewrite_as_exp(self, base, expo, **kwargs):
        from sympy import exp, log, I, arg

        if base.is_zero or base.has(exp) or expo.has(exp):
            return base ** expo

        if base.has(Symbol):
            # delay evaluation if expo is non symbolic
            # (as exp(x*log(5)) automatically reduces to x**5)
            return exp(log(base) * expo, evaluate=expo.has(Symbol))

        else:
            return exp((log(abs(base)) + I * arg(base)) * expo)

    def as_numer_denom(self):
#         if not self.is_commutative:
#             return self, S.One
        base, exp = self.as_base_exp()
        n, d = base.as_numer_denom()
        # this should be the same as ExpBase.as_numer_denom wrt
        # exponent handling
        neg_exp = exp.is_negative
        if not neg_exp and not (-exp).is_negative:
            neg_exp = exp._coeff_isneg()
        int_exp = exp.is_integer
        # the denominator cannot be separated from the numerator if
        # its sign is unknown unless the exponent is an integer, e.g.
        # sqrt(a/b) != sqrt(a)/sqrt(b) when a=1 and b=-1. But if the
        # denominator is negative the numerator and denominator can
        # be negated and the denominator (now positive) separated.
        if not (d.is_extended_real or int_exp):
            n = base
            d = S.One
        dnonpos = d.is_nonpositive
        if dnonpos:
            n, d = -n, -d
        elif dnonpos is None and not int_exp:
            n = base
            d = S.One
        if neg_exp:
            n, d = d, n
            exp = -exp
        if exp.is_infinite:
            if n is S.One and d is not S.One:
                return n, self.func(d, exp)
            if n is not S.One and d is S.One:
                return self.func(n, exp), d
        return self.func(n, exp), self.func(d, exp)

    def matches(self, expr, repl_dict={}, old=False):
        expr = _sympify(expr)

        # special case, pattern = 1 and expr.exp can match to 0
        if expr is S.One:
            d = repl_dict.copy()
            d = self.exp.matches(S.Zero, d)
            if d is not None:
                return d

        # make sure the expression to be matched is an Expr
        if not isinstance(expr, Expr):
            return

        b, e = expr.as_base_exp()

        # special case number
        sb, se = self.as_base_exp()
        if sb.is_Symbol and se.is_Integer and expr:
            if e.is_rational:
                e /= se
                if e.is_Integer:
                    return sb.matches(b ** e, repl_dict)
                return
            return sb.matches(expr ** (1 / se), repl_dict)

        d = repl_dict.copy()
        d = self.base.matches(b, d)
        if d is None:
            return None

        d = self.exp.xreplace(d).matches(e, d)
        if d is None:
            return Expr.matches(self, expr, repl_dict)
        return d

    def _eval_nseries(self, x, n, logx):
        # NOTE! This function is an important part of the gruntz algorithm
        #       for computing limits. It has to return a generalized power
        #       series with coefficients in C(log, log(x)). In more detail:
        # It has to return an expression
        #     c_0*x**e_0 + c_1*x**e_1 + ... (finitely many terms)
        # where e_i are numbers (not necessarily integers) and c_i are
        # expressions involving only numbers, the log function, and log(x).
        from sympy import ceil, collect, exp, log, O, Order, powsimp
        b, e = self.args
        if e.is_Integer:
            if e > 0:
                # positive integer powers are easy to expand, e.g.:
                # sin(x)**4 = (x - x**3/3 + ...)**4 = ...
                return expand_multinomial(self.func(b._eval_nseries(x, n=n,
                    logx=logx), e), deep=False)
            elif e is S.NegativeOne:
                # this is also easy to expand using the formula:
                # 1/(1 + x) = 1 - x + x**2 - x**3 ...
                # so we need to rewrite base to the form "1 + x"

                nuse = n
                cf = 1

                try:
                    ord = b.as_leading_term(x)
                    cf = Order(ord, x).getn()
                    if cf and cf.is_Number:
                        nuse = n + 2 * ceil(cf)
                    else:
                        cf = 1
                except NotImplementedError:
                    pass

                b_orig, prefactor = b, O(1, x)
                while prefactor.is_Order:
                    nuse += 1
                    b = b_orig._eval_nseries(x, n=nuse, logx=logx)
                    prefactor = b.as_leading_term(x)

                # express "rest" as: rest = 1 + k*x**l + ... + O(x**n)
                rest = expand_mul((b - prefactor) / prefactor)

                if rest.is_Order:
                    return 1 / prefactor + rest / prefactor + O(x ** n, x)

                k, l = rest.leadterm(x)
                if l.is_Rational and l > 0:
                    pass
                elif l.is_number and l > 0:
                    l = l.evalf()
                elif l == 0:
                    from sympy.simplify import simplify
                    k = simplify(k)
                    if k == 0:
                        # if prefactor == w**4 + x**2*w**4 + 2*x*w**4, we need to
                        # factor the w**4 out using collect:
                        return 1 / collect(prefactor, x)
                    else:
                        raise NotImplementedError()
                else:
                    raise NotImplementedError()

                if cf < 0:
                    cf = S.One / abs(cf)

                try:
                    dn = Order(1 / prefactor, x).getn()
                    if dn and dn < 0:
                        pass
                    else:
                        dn = 0
                except NotImplementedError:
                    dn = 0

                terms = [1 / prefactor]
                for m in range(1, ceil((n - dn + 1) / l * cf)):
                    new_term = terms[-1] * (-rest)
                    if new_term.is_Pow:
                        new_term = new_term._eval_expand_multinomial(
                            deep=False)
                    else:
                        new_term = expand_mul(new_term, deep=False)
                    terms.append(new_term)
                terms.append(O(x ** n, x))
                return powsimp(Add(*terms), deep=True, combine='exp')
            else:
                # negative powers are rewritten to the cases above, for
                # example:
                # sin(x)**(-4) = 1/(sin(x)**4) = ...
                # and expand the denominator:
                nuse, denominator = n, O(1, x)
                while denominator.is_Order:
                    denominator = (b ** (-e))._eval_nseries(x, n=nuse, logx=logx)
                    nuse += 1
                if 1 / denominator == self:
                    return self
                # now we have a type 1/f(x), that we know how to expand
                return (1 / denominator)._eval_nseries(x, n=n, logx=logx)

        if e.has(Symbol):
            return exp(e * log(b))._eval_nseries(x, n=n, logx=logx)

        # see if the base is as simple as possible
        bx = b
        while bx.is_Pow and bx.exp.is_Rational:
            bx = bx.base
        if bx == x:
            return self

        # work for b(x)**e where e is not an Integer and does not contain x
        # and hopefully has no other symbols

        def e2int(e):
            """return the integer value (if possible) of e and a
            flag indicating whether it is bounded or not."""
            n = e.limit(x, 0)
            infinite = n.is_infinite
            if not infinite:
                # XXX was int or floor intended? int used to behave like floor
                # so int(-Rational(1, 2)) returned -1 rather than int's 0
                try:
                    n = int(n)
                except TypeError:
                    # well, the n is something more complicated (like 1 + log(2))
                    try:
                        n = int(n.evalf()) + 1  # XXX why is 1 being added?
                    except TypeError:
                        pass  # hope that base allows this to be resolved
                n = _sympify(n)
            return n, infinite

        order = O(x ** n, x)
        ei, infinite = e2int(e)
        b0 = b.limit(x, 0)
        if infinite and (b0 is S.One or b0.has(Symbol)):
            # XXX what order
            if b0 is S.One:
                resid = (b - 1)
                if resid.is_positive:
                    return S.Infinity
                elif resid.is_negative:
                    return S.Zero
                raise ValueError('cannot determine sign of %s' % resid)

            return b0 ** ei

        if (b0 is S.Zero or b0.is_infinite):
            if infinite is not False:
                return b0 ** e  # XXX what order

            if not ei.is_number:  # if not, how will we proceed?
                raise ValueError(
                    'expecting numerical exponent but got %s' % ei)

            nuse = n - ei

            if e.is_extended_real and e.is_positive:
                lt = b.as_leading_term(x)

                # Try to correct nuse (= m) guess from:
                # (lt + rest + O(x**m))**e =
                # lt**e*(1 + rest/lt + O(x**m)/lt)**e =
                # lt**e + ... + O(x**m)*lt**(e - 1) = ... + O(x**n)
                try:
                    cf = Order(lt, x).getn()
                    nuse = ceil(n - cf * (e - 1))
                except NotImplementedError:
                    pass

            bs = b._eval_nseries(x, n=nuse, logx=logx)
            terms = bs.removeO()
            if terms.is_Add:
                bs = terms
                lt = terms.as_leading_term(x)

                # bs -> lt + rest -> lt*(1 + (bs/lt - 1))
                return ((self.func(lt, e) * self.func((bs / lt).expand(), e).nseries(
                    x, n=nuse, logx=logx)).expand() + order)

            if bs.is_Add:
                from sympy import O
                # So, bs + O() == terms
                c = Dummy('c')
                res = []
                for arg in bs.args:
                    if arg.is_Order:
                        arg = c * arg.expr
                    res.append(arg)
                bs = Add(*res)
                rv = (bs ** e).series(x).subs(c, O(1, x))
                rv += order
                return rv

            rv = bs ** e
            if terms != bs:
                rv += order
            return rv

        # either b0 is bounded but neither 1 nor 0 or e is infinite
        # b -> b0 + (b - b0) -> b0 * (1 + (b/b0 - 1))
        o2 = order * (b0 ** -e)
        z = (b / b0 - 1)
        o = O(z, x)
        if o is S.Zero or o2 is S.Zero:
            infinite = True
        else:
            if o.expr.is_number:
                e2 = log(o2.expr * x) / log(x)
            else:
                e2 = log(o2.expr) / log(o.expr)
            n, infinite = e2int(e2)
        if infinite:
            # requested accuracy gives infinite series,
            # order is probably non-polynomial e.g. O(exp(-1/x), x).
            r = 1 + z
        else:
            l = []
            g = None
            for i in range(n + 2):
                g = self._taylor_term(i, z, g)
                g = g.nseries(x, n=n, logx=logx)
                l.append(g)
            r = Add(*l)
        return expand_mul(r * b0 ** e) + order

    def _eval_as_leading_term(self, x, cdir=0):
        from sympy import exp, log
        if not self.exp.has(x):
            return self.func(self.base.as_leading_term(x), self.exp)
        return exp(self.exp * log(self.base)).as_leading_term(x)

    @cacheit
    def _taylor_term(self, n, x, *previous_terms):  # of (1 + x)**e
        from sympy import binomial
        return binomial(self.exp, n) * self.func(x, n)

    def as_content_primitive(self, radical=False, clear=True):
        """Return the tuple (R, self/R) where R is the positive Rational
        extracted from self.

        Examples
        ========

        >>> from sympy import sqrt
        >>> sqrt(4 + 4*sqrt(2)).as_content_primitive()
        (2, sqrt(1 + sqrt(2)))
        >>> sqrt(3 + 3*sqrt(2)).as_content_primitive()
        (1, sqrt(3)*sqrt(1 + sqrt(2)))

        >>> from sympy import expand_power_base, powsimp, Mul
        >>> from sympy.abc import x, y

        >>> ((2*x + 2)**2).as_content_primitive()
        (4, (x + 1)**2)
        >>> (4**((1 + y)/2)).as_content_primitive()
        (2, 4**(y/2))
        >>> (3**((1 + y)/2)).as_content_primitive()
        (1, 3**((y + 1)/2))
        >>> (3**((5 + y)/2)).as_content_primitive()
        (9, 3**((y + 1)/2))
        >>> eq = 3**(2 + 2*x)
        >>> powsimp(eq) == eq
        True
        >>> eq.as_content_primitive()
        (9, 3**(2*x))
        >>> powsimp(Mul(*_))
        3**(2*x + 2)

        >>> eq = (2 + 2*x)**y
        >>> s = expand_power_base(eq); s.is_Mul, s
        (False, (2*x + 2)**y)
        >>> eq.as_content_primitive()
        (1, (2*(x + 1))**y)
        >>> s = expand_power_base(_[1]); s.is_Mul, s
        (True, 2**y*(x + 1)**y)

        See docstring of Expr.as_content_primitive for more examples.
        """

        b, e = self.as_base_exp()
        b = _keep_coeff(*b.as_content_primitive(radical=radical, clear=clear))
        ce, pe = e.as_content_primitive(radical=radical, clear=clear)
        if b.is_Rational:
            # e
            # = ce*pe
            # = ce*(h + t)
            # = ce*h + ce*t
            # => self
            # = b**(ce*h)*b**(ce*t)
            # = b**(cehp/cehq)*b**(ce*t)
            # = b**(iceh + r/cehq)*b**(ce*t)
            # = b**(iceh)*b**(r/cehq)*b**(ce*t)
            # = b**(iceh)*b**(ce*t + r/cehq)
            h, t = pe.as_coeff_Add()
            if h.is_Rational:
                ceh = ce * h
                c = self.func(b, ceh)
                r = S.Zero
                if not c.is_Rational:
                    iceh, r = divmod(ceh.p, ceh.q)
                    c = self.func(b, iceh)
                return c, self.func(b, _keep_coeff(ce, t + r / ce / ceh.q))
        e = _keep_coeff(ce, pe)
        # b**e = (h*t)**e = h**e*t**e = c*m*t**e
        if e.is_Rational and b.is_Mul:
            h, t = b.as_content_primitive(radical=radical, clear=clear)  # h is positive
            c, m = self.func(h, e).as_coeff_Mul()  # so c is positive
            m, me = m.as_base_exp()
            if m is S.One or me == e:  # probably always true
                # return the following, not return c, m*Pow(t, e)
                # which would change Pow into Mul; we let sympy
                # decide what to do by using the unevaluated Mul, e.g
                # should it stay as sqrt(2 + 2*sqrt(5)) or become
                # sqrt(2)*sqrt(1 + sqrt(5))
                return c, self.func(_keep_coeff(m, t), e)
        return S.One, self.func(b, e)

    def is_constant(self, *wrt, **flags):
        expr = self
        if flags.get('simplify', True):
            from sympy.simplify import simplify
            expr = simplify(expr)
        b, e = expr.as_base_exp()
        bz = b.equals(0)
        if bz:  # recalculate with assumptions in case it's unevaluated
            new = b ** e
            if new != expr:
                return new.is_constant()
        econ = e.is_constant(*wrt)
        bcon = b.is_constant(*wrt)
        if bcon:
            if econ:
                return True
            bz = b.equals(0)
            if bz is False:
                return False
        elif bcon is None:
            return None

        return e.equals(0)

    def _eval_difference_delta(self, n, step):
        b, e = self.args
        if e.has(n) and not b.has(n):
            new_e = e.subs(n, n + step)
            return (b ** (new_e - e) - 1) * self

    def domain_nonzero(self, x):
        domain = self.base.domain_nonzero(x)
        if self.exp > 0:
            return domain & self.domain_defined(x)
        if self.exp < 0:
            return domain & self.domain_defined(x)
        return self.domain_defined(x)

    @cacheit
    def _eval_domain_defined(self, x, **kwargs):
        domain = self.base.domain_defined(x) & self.exp.domain_defined(x)
        if self.exp < 0:
            domain &= self.base.domain_nonzero(x)
        if self.exp.is_integer == False:
            if x.is_real and kwargs.get('real'):
                domain &= x.domain_conditioned(self.base >= 0)
        return domain

    def _eval_Abs(self):
        from sympy import exp, log, Abs, Re, Im
        base, exponent = self.as_base_exp()
        if base.is_extended_real:
            if exponent.is_integer:
                if exponent.is_even:
                    return self
                if base is S.NegativeOne:
                    return S.One
                if isinstance(base, Abs) and exponent is S.NegativeOne:
                    return self
                return Abs(base) ** exponent
            if base.is_extended_nonnegative:
                return base ** Re(exponent)
            if base.is_extended_negative:
                return (-base) ** Re(exponent) * exp(-S.Pi * Im(exponent))
            return
        elif not base.has(Symbol):  # complex base
            # express base**exponent as exp(exponent*log(base))
            a, b = log(base).as_real_imag()
            z = a + S.ImaginaryUnit * b
            return exp(Re(exponent * z))
        elif not self.is_complex and not exponent.is_integer:
            return self

    def _latex(self, p):
        # Treat x**Rational(1,n) as special case
        if self.exp.is_Rational and abs(self.exp.p) == 1 and self.exp.q != 1 \
                and p._settings['root_notation']:
            base = p._print(self.base)
            expq = self.exp.q

            if expq == 2:
                tex = r"\sqrt{%s}" % base
            elif p._settings['itex']:
                tex = r"\root{%d}{%s}" % (expq, base)
            else:
                tex = r"\sqrt[%d]{%s}" % (expq, base)

            if self.exp.is_negative:
                return r"\frac{1}{%s}" % tex
            else:
                return tex
        elif p._settings['fold_frac_powers'] \
            and self.exp.is_Rational \
                and self.exp.q != 1:
            from sympy.printing.precedence import PRECEDENCE
            base = p.parenthesize(self.base, PRECEDENCE['Pow'])
            p, q = self.exp.p, self.exp.q
            # issue #12886: add parentheses for superscripts raised to powers
            if '^' in base and self.base.is_Symbol:
                base = r"\left(%s\right)" % base
            if self.base.is_Function:
                return p._print(self.base, exp="%s/%s" % (p, q))
            return r"%s^{%s/%s}" % (base, p, q)
        elif self.exp.is_Rational and self.exp.is_negative:
            # special case for 1^(-x), issue 9216
            if self.base == 1:
                return r"%s^{%s}" % (self.base, self.exp)
            # things like 1/x
            from sympy.core.mul import Mul
            return Mul._latex(self, p)
        else:
            if self.base.is_Piecewise:
                tex = r"\left(%s\right)^{%s}"
                return p._helper_print_standard_power(self, tex)
            elif self.base.is_Function:
                return p._print(self.base, exp=p._print(self.exp))
            else:
                tex = r"%s^{%s}"
                return p._helper_print_standard_power(self, tex)

    def _sympystr(self, p, rational=False):
        from sympy.printing.precedence import precedence
        PREC = precedence(self)

        import re
        if self.exp is S.Half and not rational:
            arg = p._print(self.base)
            # return "\N{SQUARE ROOT}(%s)" % arg
            return "sqrt(%s)" % arg

#         if self.is_commutative:
        if -self.exp is S.Half and not rational:
            # Note: Don't test "self.exp == -S.Half" here, because that will
            # match -0.5, which we don't want.
            arg = p._print(self.base)
            # return "1/\N{SQUARE ROOT}(%s)" % arg
            return "1 / sqrt(%s)" % arg
        
        if self.exp is -S.One:
            # Similarly to the S.Half case, don't test with "==" here.
            return '%s / %s' % (p._print(S.One),
                              p.parenthesize(self.base, PREC, strict=False))

        e = p.parenthesize(self.exp, PREC, strict=False)
        if p.printmethod == '_sympyrepr' and self.exp.is_Rational and self.exp.q != 1:
            # the parenthesized exp should be '(Rational(a, b))' so strip parens,
            # but just check to be sure.
            if e.startswith('(Rational'):
                return '%s ** %s' % (p.parenthesize(self.base, PREC, strict=False), e[1:-1])
        return '%s ** %s' % (p.parenthesize(self.base, PREC, strict=False), e)
    
    def _lean(self, p, rational=False):
        from sympy.printing.precedence import precedence
        PREC = precedence(self)

        import re
        if self.exp is S.Half and not rational:
            arg = p._print(self.base)
            # return "\N{SQUARE ROOT}(%s)" % arg
            return "sqrt(%s)" % arg

#         if self.is_commutative:
        if -self.exp is S.Half and not rational:
            # Note: Don't test "self.exp == -S.Half" here, because that will
            # match -0.5, which we don't want.
            arg = p._print(self.base)
            # return "1/\N{SQUARE ROOT}(%s)" % arg
            return "1 / sqrt(%s)" % arg
        
        if self.base.is_Function:
            b = "(%s)" % p._print(self.base)
        else:
            b = p.parenthesize(self.base, PREC, strict=False)

        e = self.exp
        if e == -1:
            e = '⁻¹'
        elif e == 2:
            e = '²'
        elif e == 3:
            e = '³'
        elif e == 4:
            e = '⁴'
        else:
            e = None
        if e:
            return f'{b}{e}'

        e = p.parenthesize(self.exp, PREC, strict=False)
        if p.printmethod == '_sympyrepr' and self.exp.is_Rational and self.exp.q != 1:
            # the parenthesized exp should be '(Rational(a, b))' so strip parens,
            # but just check to be sure.
            if e.startswith('(Rational'):
                return f'{b} ^ %s' % e[1:-1]
        return f'{b} ^ %s' % e

    def _pretty(self, p):
        from sympy.simplify.simplify import fraction
        b, e = self.as_base_exp()
        from sympy.printing.pretty.stringpict import prettyForm
        
        if e is S.NegativeOne:
            return prettyForm("1") / p._print(b)
        n, d = fraction(e)
        if n is S.One and d.is_Atom and not e.is_Integer and p._settings['root_notation']:
            return p._print_nth_root(b, e)
        if e.is_Rational and e < 0:
            return prettyForm("1") / p._print(Pow(b, -e, evaluate=False))

        if b.is_Relational:
            return prettyForm(*p._print(b).parens()).__pow__(p._print(e))

        return p._print(b) ** p._print(e)
    
    def _eval_is_random(self):
        for arg in self.args:
            if arg.is_random:
                return True
    
    def domain_definition(self, **_):
        if self.exp.is_extended_negative:
            from sympy import Unequal
            shape = self.base.shape
            if shape:
                excludes = set()
                vars = []
                limits = []
                for n in shape:
                    i = self.generate_var(excludes, integer=True)
                    vars.append(i)
                    excludes.add(i)
                    limits.append((i, 0, n))
                limits.reverse()
                
                from sympy import All
                return All(Unequal(self.base[tuple(vars)], 0), *limits) 
            else:
                return Unequal(self.base, 0)
        return S.true
    
    def simplify(self, deep=False, **kwargs):
        if deep:
            return Expr.simplify(self, deep)
        
        base, exp = self.args
        if exp.is_Integer:
            if {*base.enumerate_KroneckerDelta()}:
                return self.expand()
            
        elif exp == S.Half:
            if base.is_Mul:
                if all(b.is_Pow and b.exp.is_even for b in base.args):
                    return abs(base.func(*(b.base ** (b.exp // 2) for b in base.args)))
                    
        return self

    def of(self, cls):
        res = Expr.of(self, cls)
        if res is None:
            if cls.is_Pow:
                base, exp = cls.args
                if exp == -1 and self.exp._coeff_isneg():
                    self = self.func(self.base, -self.exp)
                    if not base.is_abstract:
                        self = self.of(base)
                    return self
                                             
        return res
    
    def __invert__(self):
        from sympy import Conjugate
        b, e = self.args
        if e.is_integer:
            return Conjugate(b) ** e
        return Conjugate(self)

    @staticmethod
    def simplify_Lamda(self, squeeze=False):
        expr, *limits = self.args
        b, e = expr.args
        if e.shape:
            if not b.shape:
                if e.has(*self.variables):
                    lamda = self.func(e, *self.limits)
                    _lamda = lamda.simplify()
                    if lamda != _lamda:
                        return expr.func(b, _lamda, evaluate=False)
                
        else:
            if b.has(*self.variables):
                lamda = self.func(b, *self.limits)
                _lamda = lamda.simplify()
                if lamda != _lamda:
                    return expr.func(_lamda, e, evaluate=False)

        return self
    
    def monotonicity(self, x):
        b, e = self.args
        if e < 0:
            if e._has(x):
                ...
            else:
                if e.is_integer:
                    if b > 0 or b < 0:
                        expr, monotonicity = b.monotonicity(x)
                        if not monotonicity:
                            return None, 0
                        
                        return expr ** e, -monotonicity

        elif e > 0:
            if e._has(x):
                if b > 0:
                    if b._has(x):
                        ...
                    else:
                        expr, monotonicity = e.monotonicity(x)
                        if not monotonicity:
                            return None, 0
                        
                        return b ** expr, monotonicity
            else:
                if b > 0:
                    expr, monotonicity = b.monotonicity(x)
                    if not monotonicity:
                        return None, 0
                    
                    return expr ** e, monotonicity

        return None, 0

    @cacheit
    def sort_key(self, order=None):
        expr, exp = self.args

        if expr.is_Dummy:
            args = (expr.sort_key(),)
        elif expr.is_Atom:
            args = (str(expr),)
        else:
            if expr.is_Add:
                args = expr.as_ordered_terms(order=order)
            elif expr.is_Mul:
                args = expr.as_ordered_factors(order=order)
            else:
                args = expr.args

            args = tuple(arg.sort_key(order=order) for arg in args)

        args = len(args), tuple(arg.class_key() for arg in self.args), args
        exp = exp.sort_key(order=order)

        return expr.class_key(), args, exp, S.One

    def doit(self, **kwargs):
        if kwargs.get('deep'):
            b, e = self.args
            b = b.doit(deep=True)
            e = e.doit(deep=True)
            if e.is_DenseMatrix:
                if not b.shape:
                    from sympy import Matrix
                    return Matrix(tuple(b ** e for e in e._args), shape=e.shape)
            return b ** e
        return self

    def is_continuous_at(self, *args):
        x, *ab = args
        b, e = self.args
        if b._has(x):
            if b >= 0 and e >= 0:
                return True
            return
        
        if e._has(x):
            if b >= 0 and e >= 0:
                return True
            return
        
        return True

    def _eval_try_div(self, factor):
        b, e = self.args
        if b == factor:
            if e >= 1:
                return b ** (e - 1)

        elif factor.is_Pow and b == factor.base:
            if (diff := e - factor.exp) >= 0:
                return b ** diff

    def extract_pow(self, x):
        by, ey = self.args
        if by == x:
            if ey.is_Integer and ey > 1:
                return x

            elif ey.is_Add:
                if any(e.is_Integer and e >= 1 for e in ey.args):
                    return x

        elif x.is_Pow:
            bx, ex = x.args
            if bx == by:
                if ex.is_Add:
                    argset = {*ex.args}
                    if ey in argset or ey.is_Add and all(e in argset for e in ey.args):
                        return self

                if ex.is_Integer and ey.is_Integer:
                    if ex > 0 and ey > 0:
                        return bx ** min(ex, ey)

                    if ex < 0 and ey < 0:
                        return bx ** max(ex, ey)

from .add import Add
from .numbers import Integer
from .mul import Mul, _keep_coeff
from .symbol import Symbol, Dummy, symbols


def cbrt(arg, evaluate=None):
    """This function computes the principal cube root of `arg`, so
    it's just a shortcut for `arg**Rational(1, 3)`.

    The parameter evaluate determines if the expression should be evaluated.
    If None, its value is taken from global_evaluate.

    Examples
    ========

    >>> from sympy import cbrt, Symbol
    >>> x = Symbol('x')

    >>> cbrt(x)
    x**(1/3)

    >>> cbrt(x)**3
    x

    Note that cbrt(x**3) does not simplify to x.

    >>> cbrt(x**3)
    (x**3)**(1/3)

    This is because the two are not equal to each other in general.
    For example, consider `x == -1`:

    >>> from sympy import Eq
    >>> Eq(cbrt(x**3), x).subs(x, -1)
    False

    This is because cbrt computes the principal cube root, this
    identity does hold if `x` is positive:

    >>> y = Symbol('y', positive=True)
    >>> cbrt(y**3)
    y

    See Also
    ========

    sympy.polys.rootoftools.rootof, root, real_root

    References
    ==========

    * https://en.wikipedia.org/wiki/Cube_root
    * https://en.wikipedia.org/wiki/Principal_value

    """
    from sympy import Rational
    return Pow(arg, Rational(1, 3), evaluate=evaluate)


def root(arg, n, k=0, evaluate=None):
    """root(x, n, k) -> Returns the k-th n-th root of x, defaulting to the
    principal root (k=0).

    The parameter evaluate determines if the expression should be evaluated.
    If None, its value is taken from global_evaluate.

    Examples
    ========

    >>> from sympy import root, Rational
    >>> from sympy.abc import x, n

    >>> root(x, 2)
    sqrt(x)

    >>> root(x, 3)
    x**(1/3)

    >>> root(x, n)
    x**(1/n)

    >>> root(x, -Rational(2, 3))
    x**(-3/2)

    To get the k-th n-th root, specify k:

    >>> root(-2, 3, 2)
    -(-1)**(2/3)*2**(1/3)

    To get all n n-th roots you can use the rootof function.
    The following examples show the roots of unity for n
    equal 2, 3 and 4:

    >>> from sympy import rootof, I

    >>> [rootof(x**2 - 1, i) for i in range(2)]
    [-1, 1]

    >>> [rootof(x**3 - 1,i) for i in range(3)]
    [1, -1/2 - sqrt(3)*I/2, -1/2 + sqrt(3)*I/2]

    >>> [rootof(x**4 - 1,i) for i in range(4)]
    [-1, 1, -I, I]

    SymPy, like other symbolic algebra systems, returns the
    complex root of negative numbers. This is the principal
    root and differs from the text-book result that one might
    be expecting. For example, the cube root of -8 does not
    come back as -2:

    >>> root(-8, 3)
    2*(-1)**(1/3)

    The real_root function can be used to either make the principal
    result real (or simply to return the real root directly):

    >>> from sympy import real_root
    >>> real_root(_)
    -2
    >>> real_root(-32, 5)
    -2

    Alternatively, the n//2-th n-th root of a negative number can be
    computed with root:

    >>> root(-32, 5, 5//2)
    -2

    See Also
    ========

    sympy.polys.rootoftools.rootof
    sympy.core.power.integer_nthroot
    sqrt, real_root

    References
    ==========

    * https://en.wikipedia.org/wiki/Square_root
    * https://en.wikipedia.org/wiki/Real_root
    * https://en.wikipedia.org/wiki/Root_of_unity
    * https://en.wikipedia.org/wiki/Principal_value
    * http://mathworld.wolfram.com/CubeRoot.html

    """
    from sympy import sympify
    n = sympify(n)
    if k:
        return Mul(Pow(arg, S.One / n, evaluate=evaluate), S.NegativeOne ** (2 * k / n), evaluate=evaluate)
    return Pow(arg, 1 / n, evaluate=evaluate)


def real_root(arg, n=None, evaluate=None):
    """Return the real nth-root of arg if possible. If n is omitted then
    all instances of (-n)**(1/odd) will be changed to -n**(1/odd); this
    will only create a real root of a principal root -- the presence of
    other factors may cause the result to not be real.

    The parameter evaluate determines if the expression should be evaluated.
    If None, its value is taken from global_evaluate.

    Examples
    ========

    >>> from sympy import root, real_root, Rational
    >>> from sympy.abc import x, n

    >>> real_root(-8, 3)
    -2
    >>> root(-8, 3)
    2*(-1)**(1/3)
    >>> real_root(_)
    -2

    If one creates a non-principal root and applies real_root, the
    result will not be real (so use with caution):

    >>> root(-8, 3, 2)
    -2*(-1)**(2/3)
    >>> real_root(_)
    -2*(-1)**(2/3)


    See Also
    ========

    sympy.polys.rootoftools.rootof
    sympy.core.power.integer_nthroot
    root, sqrt
    """
    from sympy.functions.elementary.complexes import Abs, Im, sign
    from sympy.functions.elementary.piecewise import Piecewise
    from sympy import Or, Eq, And, Mod, sympify
    from sympy.core.rules import Transform
    if n is not None:
        return Piecewise(
            (root(arg, n, evaluate=evaluate), Or(Eq(n, S.One), Eq(n, S.NegativeOne))),
            (Mul(sign(arg), root(Abs(arg), n, evaluate=evaluate), evaluate=evaluate),
            And(Eq(Im(arg), S.Zero), Eq(Mod(n, 2), S.One))),
            (root(arg, n, evaluate=evaluate), True))
    rv = sympify(arg)
    n1pow = Transform(lambda x:-(-x.base) ** x.exp,
                      lambda x:
                      x.is_Pow and
                      x.base.is_negative and
                      x.exp.is_Rational and
                      x.exp.p == 1 and x.exp.q % 2)
    return rv.xreplace(n1pow)

###############################################################################
############################# MINIMUM and MAXIMUM #############################
###############################################################################

