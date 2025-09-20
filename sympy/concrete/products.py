
from sympy.core.mul import Mul
from sympy.core.singleton import S
from sympy.concrete.expr_with_intlimits import ExprWithIntLimits
from sympy.core.exprtools import factor_terms
from sympy.functions.elementary.exponential import exp, log
from sympy.polys import quo, roots
from sympy.simplify import powsimp
from sympy.matrices.expressions.matmul import MatMul
from sympy.matrices.expressions.matexpr import MatrixExpr
from sympy.core.containers import Tuple


class Product(ExprWithIntLimits):
    r"""Represents unevaluated products.

    ``Product`` represents a finite or infinite product, with the first
    argument being the general form of terms in the series, and the second
    argument being ``(dummy_variable, start, end)``, with ``dummy_variable``
    taking all integer values from ``start`` through ``end``. In accordance
    with long-standing mathematical convention, the end term is included in
    the product.

    Finite products
    ===============

    For finite products (and products with symbolic limits assumed to be finite)
    we follow the analogue of the summation convention described by Karr [1],
    especially definition 3 of section 1.4. The product:

    .. math::

        \prod_{m \leq i < n} f(i)

    has *the obvious meaning* for `m < n`, namely:

    .. math::

        \prod_{m \leq i < n} f(i) = f(m) f(m+1) \cdot \ldots \cdot f(n-2) f(n-1)

    with the upper limit value `f(n)` excluded. The product over an empty set is
    one if and only if `m = n`:

    .. math::

        \prod_{m \leq i < n} f(i) = 1  \quad \mathrm{for} \quad  m = n

    Finally, for all other products over empty sets we assume the following
    definition:

    .. math::

        \prod_{m \leq i < n} f(i) = \frac{1}{\prod_{n \leq i < m} f(i)}  \quad \mathrm{for} \quad  m > n

    It is important to note that above we define all products with the upper
    limit being exclusive. This is in contrast to the usual mathematical notation,
    but does not affect the product convention. Indeed we have:

    .. math::

        \prod_{m \leq i < n} f(i) = \prod_{i = m}^{n - 1} f(i)

    where the difference in notation is intentional to emphasize the meaning,
    with limits typeset on the top being inclusive.

    Examples
    ========

    >>> from sympy.abc import a, b, i, k, m, n, x
    >>> from sympy import Product, factorial, oo
    >>> Product(k, (k, 1, m))
    Product(k, (k, 1, m))
    >>> Product(k, (k, 1, m)).doit()
    factorial(m)
    >>> Product(k**2,(k, 1, m))
    Product(k**2, (k, 1, m))
    >>> Product(k**2,(k, 1, m)).doit()
    factorial(m)**2

    Wallis' product for pi:

    >>> W = Product(2*i/(2*i-1) * 2*i/(2*i+1), (i, 1, oo))
    >>> W
    Product(4*i**2/((2*i - 1)*(2*i + 1)), (i, 1, oo))

    Direct computation currently fails:

    >>> W.doit()
    Product(4*i**2/((2*i - 1)*(2*i + 1)), (i, 1, oo))

    But we can approach the infinite product by a limit of finite products:

    >>> from sympy import limit
    >>> W2 = Product(2*i/(2*i-1)*2*i/(2*i+1), (i, 1, n))
    >>> W2
    Product(4*i**2/((2*i - 1)*(2*i + 1)), (i, 1, n))
    >>> W2e = W2.doit()
    >>> W2e
    2**(-2*n)*4**n*factorial(n)**2/(RisingFactorial(1/2, n)*RisingFactorial(3/2, n))
    >>> limit(W2e, n, oo)
    pi/2

    By the same formula we can compute sin(pi/2):

    >>> from sympy import pi, gamma, simplify
    >>> P = pi * x * Product(1 - x**2/k**2, (k, 1, n))
    >>> P = P.subs(x, pi/2)
    >>> P
    pi**2*Product(1 - pi**2/(4*k**2), (k, 1, n))/2
    >>> Pe = P.doit()
    >>> Pe
    pi**2*RisingFactorial(1 - pi/2, n)*RisingFactorial(1 + pi/2, n)/(2*factorial(n)**2)
    >>> Pe = Pe.rewrite(gamma)
    >>> Pe
    pi**2*gamma(n + 1 + pi/2)*gamma(n - pi/2 + 1)/(2*gamma(1 - pi/2)*gamma(1 + pi/2)*gamma(n + 1)**2)
    >>> Pe = simplify(Pe)
    >>> Pe
    sin(pi**2/2)*gamma(n + 1 + pi/2)*gamma(n - pi/2 + 1)/gamma(n + 1)**2
    >>> limit(Pe, n, oo)
    sin(pi**2/2)

    Products with the lower limit being larger than the upper one:

    >>> Product(1/i, (i, 6, 1)).doit()
    120
    >>> Product(i, (i, 2, 5)).doit()
    120

    The empty product:

    >>> Product(i, (i, n, n-1)).doit()
    1

    An example showing that the symbolic result of a product is still
    valid for seemingly nonsensical values of the limits. Then the Karr
    convention allows us to give a perfectly valid interpretation to
    those products by interchanging the limits according to the above rules:

    >>> P = Product(2, (i, 10, n)).doit()
    >>> P
    2**(n - 9)
    >>> P.subs(n, 5)
    1/16
    >>> Product(2, (i, 10, 5)).doit()
    1/16
    >>> 1/Product(2, (i, 6, 9)).doit()
    1/16

    An explicit example of the Karr summation convention applied to products:

    >>> P1 = Product(x, (i, a, b)).doit()
    >>> P1
    x**(-a + b + 1)
    >>> P2 = Product(x, (i, b+1, a-1)).doit()
    >>> P2
    x**(a - b - 1)
    >>> simplify(P1 * P2)
    1

    And another one:

    >>> P1 = Product(i, (i, b, a)).doit()
    >>> P1
    RisingFactorial(b, a - b + 1)
    >>> P2 = Product(i, (i, a+1, b-1)).doit()
    >>> P2
    RisingFactorial(a + 1, -a + b - 1)
    >>> P1 * P2
    RisingFactorial(b, a - b + 1)*RisingFactorial(a + 1, -a + b - 1)
    >>> simplify(P1 * P2)
    1

    See Also
    ========

    Sum, summation
    product

    References
    ==========

    .. [1] Michael Karr, "Summation in Finite Terms", Journal of the ACM,
           Volume 28 Issue 2, April 1981, Pages 305-350
           http://dl.acm.org/citation.cfm?doid=322248.322255
    .. [2] https://en.wikipedia.org/wiki/Multiplication#Capital_Pi_notation
    .. [3] https://en.wikipedia.org/wiki/Empty_product
    """

    __slots__ = ['is_commutative']
    is_complex = True
    operator = Mul
    
    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithIntLimits.__new__(cls, function, *symbols, **assumptions)

    def _eval_rewrite_as_Sum(self, *args, **kwargs):
        from sympy.concrete.summations import Sum
        return exp(Sum(log(self.expr), *self.limits))

    @property
    def term(self):
        return self._args[0]

    function = term

    def _eval_is_zero(self):
        # a Product is zero only if its term is zero.
        function = self.expr
        from sympy import Range
        reps = {}
        for limit in self.limits[::-1]:
            x, *ab = limit
            if len(ab) == 1:
                domain, *_ = ab
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
                reps[x] = _x
            elif len(ab) == 2:
                a, b = ab
                if a.free_symbols & reps.keys():
                    a = a.subs(reps)
                    
                if b.free_symbols & reps.keys():
                    b = b.subs(reps)
                _x = x.copy(domain=Range(a, b))
                function = function._subs(x, _x)
                reps[x] = _x
                
        return function.is_zero

    def doit(self, **hints):
        f = self.expr
        
        for index, limit in enumerate(self.limits):
            if len(limit) == 1:
                i = limit[0]
                domain = self.expr.domain_defined(i)
                if domain.is_Range: 
                    a, b = domain.start, domain.stop
                else:
                    return self
            else:
                i, a, b = limit
                
            dif = b - a
            if dif.is_Integer and dif < 0:
                a, b = b + 1, a - 1
                f = 1 / f

            g = self._eval_product(f, (i, a, b))
            if g in (None, S.NaN): 
                if index < len(self.limits) - 1:
                    i, a, b = self.limits[-1]
                    dif = b - a
                    if dif.is_Integer:
                        limits = self.limits[index:-1]
                        args = []
                        for index in range(dif):
                            _i = a + index
                            args.append(self.func(f._subs(i, _i), *[limit._subs(i, _i) for limit in limits]).simplify())
                            
                        return self.operator(*args)
                if index == 0:
                    return self.simplify()
                
                return self.func(powsimp(f), *self.limits[index:]).simplify()
            else:
                f = g

        if hints.get('deep', True):
            return f.doit(**hints)
        else:
            return powsimp(f)

    def _eval_adjoint(self):
        if self.is_commutative:
            return self.func(self.expr.adjoint(), *self.limits)
        return None

    def _eval_conjugate(self):
        return self.func(self.expr.conjugate(), *self.limits)

    def _eval_product(self, term, limits):
        from sympy.concrete.delta import deltaproduct, _has_simple_delta
        from sympy.concrete.summations import summation
        from sympy.functions import KroneckerDelta, RisingFactorial

        (k, a, n1) = limits

        if k not in term.free_symbols:
            if (term - 1).is_zero:
                return S.One
            return term ** (n1 - a)

        if a == n1 - 1:
            return term.subs(k, a)

        if term.has(KroneckerDelta) and _has_simple_delta(term, limits[0]):
            return deltaproduct(term, limits)

        dif = n1 - a
        if dif.is_Integer:
            return Mul(*[term.subs(k, a + i) for i in range(dif)])

        elif term.is_polynomial(k):
            poly = term.as_poly(k)

            A = B = Q = S.One

            all_roots = roots(poly)

            M = 0
            for r, m in all_roots.items():
                M += m
                A *= RisingFactorial(a - r, n1 - a) ** m
                Q *= (n1 - 1 - r) ** m

            if M < poly.degree():
                arg = quo(poly, Q.as_poly(k))
                B = self.func(arg, limits).doit()

            return poly.LC() ** (n1 - a) * A * B

        elif term.is_Add:
            factored = factor_terms(term, fraction=True)
            if factored.is_Mul:
                return self._eval_product(factored, limits)

        elif term.is_Mul:
            exclude, include = [], []

            for t in term.args:
                p = self._eval_product(t, limits)

                if p is not None:
                    exclude.append(p)
                else:
                    include.append(t)

            if not exclude:
                return None
            else:
                arg = term._new_rawargs(*include)
                A = Mul(*exclude)
                B = self.func(arg, limits).doit()
                return A * B

        elif term.is_Pow:
            if not term.base.has(k):
                s = summation(term.exp, limits)

                return term.base ** s
            elif not term.exp.has(k):
                p = self._eval_product(term.base, limits)

                if p is not None:
                    return p ** term.exp

        elif isinstance(term, Product):
            evaluated = term.doit()
            f = self._eval_product(evaluated, limits)
            if f is None:
                return self.func(evaluated, limits)
            else:
                return f

    def _eval_simplify(self, ratio, measure, rational, inverse):
        from sympy.simplify.simplify import product_simplify
        return product_simplify(self)

    def _eval_transpose(self, *axis):
        if axis == self.default_axis: 
            return self.func(self.expr.transpose(), *self.limits)        

    def _eval_is_finite(self):
        function = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                if domain.is_infinite:
                    return None
                    
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_finite

    def _eval_is_extended_real(self):
        function = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                if _x != x:
                    function = function._subs(x, _x)
                
        return function.is_extended_real

    def _eval_is_extended_positive(self):
        function = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                if domain.is_infinite:
                    return
                    
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_positive

    def _eval_is_extended_negative(self):
        function = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                if domain.is_infinite:
                    return
                    
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_negative

    def is_convergent(self):
        r"""
        See docs of Sum.is_convergent() for explanation of convergence
        in SymPy.

        The infinite product:

        .. math::

            \prod_{1 \leq i < \infty} f(i)

        is defined by the sequence of partial products:

        .. math::

            \prod_{i=1}^{n} f(i) = f(1) f(2) \cdots f(n)

        as n increases without bound. The product converges to a non-zero
        value if and only if the sum:

        .. math::

            \sum_{1 \leq i < \infty} \log{f(n)}

        converges.

        Examples
        ========

        >>> from sympy import Interval, S, Product, Symbol, cos, pi, exp, oo
        >>> n = Symbol('n', integer=True)
        >>> Product(n/(n + 1), (n, 1, oo)).is_convergent()
        False
        >>> Product(1/n**2, (n, 1, oo)).is_convergent()
        False
        >>> Product(cos(pi/n), (n, 1, oo)).is_convergent()
        True
        >>> Product(exp(-n**2), (n, 1, oo)).is_convergent()
        False

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Infinite_product
        """
        from sympy.concrete.summations import Sum

        sequence_term = self.expr
        log_sum = log(sequence_term)
        lim = self.limits
        try:
            is_conv = Sum(log_sum, *lim).is_convergent()
        except NotImplementedError:
            if Sum(sequence_term - 1, *lim).is_absolutely_convergent() is S.true:
                return S.true
            raise NotImplementedError("The algorithm to find the product convergence of %s "
                                        "is not yet implemented" % (sequence_term))
        return is_conv

    def reverse_order(expr, *indices):
        """
        Reverse the order of a limit in a Product.

        Usage
        =====

        ``reverse_order(expr, *indices)`` reverses some limits in the expression
        ``expr`` which can be either a ``Sum`` or a ``Product``. The selectors in
        the argument ``indices`` specify some indices whose limits get reversed.
        These selectors are either variable names or numerical indices counted
        starting from the inner-most limit tuple.

        Examples
        ========

        >>> from sympy import Product, simplify, RisingFactorial, gamma, Sum
        >>> from sympy.abc import x, y, a, b, c, d
        >>> P = Product(x, (x, a, b))
        >>> Pr = P.reverse_order(x)
        >>> Pr
        Product(1/x, (x, b + 1, a - 1))
        >>> Pr = Pr.doit()
        >>> Pr
        1/RisingFactorial(b + 1, a - b - 1)
        >>> simplify(Pr)
        gamma(b + 1)/gamma(a)
        >>> P = P.doit()
        >>> P
        RisingFactorial(a, -a + b + 1)
        >>> simplify(P)
        gamma(b + 1)/gamma(a)

        While one should prefer variable names when specifying which limits
        to reverse, the index counting notation comes in handy in case there
        are several symbols with the same name.

        >>> S = Sum(x*y, (x, a, b), (y, c, d))
        >>> S
        Sum(x*y, (x, a, b), (y, c, d))
        >>> S0 = S.reverse_order(0)
        >>> S0
        Sum(-x*y, (x, b + 1, a - 1), (y, c, d))
        >>> S1 = S0.reverse_order(1)
        >>> S1
        Sum(x*y, (x, b + 1, a - 1), (y, d + 1, c - 1))

        Of course we can mix both notations:

        >>> Sum(x*y, (x, a, b), (y, 2, 5)).reverse_order(x, 1)
        Sum(x*y, (x, b + 1, a - 1), (y, 6, 1))
        >>> Sum(x*y, (x, a, b), (y, 2, 5)).reverse_order(y, x)
        Sum(x*y, (x, b + 1, a - 1), (y, 6, 1))

        See Also
        ========

        index, reorder_limit, reorder

        References
        ==========

        .. [1] Michael Karr, "Summation in Finite Terms", Journal of the ACM,
               Volume 28 Issue 2, April 1981, Pages 305-350
               http://dl.acm.org/citation.cfm?doid=322248.322255
        """
        l_indices = list(indices)

        for i, indx in enumerate(l_indices):
            if not isinstance(indx, int):
                l_indices[i] = expr.index(indx)

        e = 1
        limits = []
        for i, limit in enumerate(expr.limits):
            l = limit
            if i in l_indices:
                e = -e
                l = (limit[0], limit[2] + 1, limit[1] - 1)
            limits.append(l)

        return Product(expr.expr ** e, *limits)

    def simplify(self, deep=False, **_):
        limits_dict = self.limits_dict

        for i, (x, *_) in enumerate(self.limits):
            domain = limits_dict[x]
            if domain is None or isinstance(domain, list):
                continue
            if self.expr._has(x): 
                if domain.is_set and self.expr.domain_defined(x) in domain:
                    limits = [*self.limits]
                    limits[i] = (x,)
                    return self.func(self.expr, *limits).simplify()
        
        if len(self.limits) > 1:
            limit = self.limits[-1]
            if len(limit) == 3:
                function = self.func(self.expr, *self.limits[:-1])
                x, a, b = limit
                if not function._has(x):
                    return function ** (b - a)
                
                if a == b - 1: 
                    return function._subs(x, a).simplify(deep=deep)
                if a >= b:
                    return S.One
            return self
        
        limit = self.limits[0]
        if len(limit) == 1:
            x = limit[0]
            domain = x.domain
            if domain.is_Range: 
                limit = x, domain.start, domain.stop

        if len(limit) == 2:
            x, domain = limit
            if domain.is_FiniteSet and len(domain) == 1:
                return self.finite_aggregate(x, domain)
            if not self.expr._has(x):
                from sympy import Card
                return self.expr ** Card(domain)
                            
        elif len(limit) == 3:
            x, a, b = limit
            if self.expr.is_Piecewise:
                from sympy import Range
                return self.expr.as_multiple_terms(x, Range(a, b), self.func)
            if not self.expr._has(x):
                return self.expr ** (b - a)
            
            if self.expr.is_Mul:
                if len(self.expr.args) == 2:
                    fx1, fx = self.expr.args
                    if fx1.is_Pow and fx1.exp == -1:
                        fx1, fx = fx, fx1
                        hit = True    
                    elif fx.is_Pow and fx.exp == -1:
                        hit = True
                    else:
                        hit = False
                        
                    if hit:
                        fx = 1 / fx
                        from sympy import Wild
                        pattern = fx.subs(x, Wild(x.name, **x.assumptions0))

                        res = fx1.match(pattern)
                        if res:
                            x_, *_ = res.values()
                            if x_ == x + 1:
                                return fx1._subs(x, b - 1) / fx._subs(x, a)
            if a == b - 1: 
                return self.expr._subs(x, a)
            if a >= b:
                return S.One
        else:
            x, *_ = limit
        function = self.expr
        independent, dependent = function.as_independent(x, as_Add=False)
        if independent == S.One:
            return self

        if dependent == S.One:
            if len(limit) > 1:
                return self.expr ** (b - a)
            else:
                return self.expr ** x.dimension
        if len(limit) > 1:
            return self.func(dependent, limit).doit() * independent ** (b - a)
        else:
            return self.func(dependent, limit).doit() * independent ** x.dimension

    def _sympystr(self, p):
        limits = ','.join([':'.join([p._print(arg) for arg in limit]) for limit in self.limits])
        return 'Product[%s](%s)' % (limits, p._print(self.expr))

    def _lean(self, p):
        operator = '\N{N-ARY PRODUCT}'
        limits = [limit._format_ineq(p) for limit in self.limits]
        operator = ", ".join(reversed(["%s %s" % (operator, limit) for limit in limits]))
        operator = operator.replace('%', '%%')
        return f'{operator}, %s' % p._print(self.expr)

    latex_name_of_operator = 'prod'

    def try_absorb(self, expr):
        if len(self.limits) == 1:
            i, *ab = self.limits[0]
            if len(ab) == 2 and expr:
                a, b = ab
                if self.expr.subs(i, b) == expr:
                    return self.func(self.expr, (i, a, b + 1)).simplify()
                if self.expr.subs(i, a - 1) == expr:
                    return self.func(self.expr, (i, a - 1 , b)).simplify()

    def as_two_terms(self):
        first, second = self.expr.as_two_terms()
        if isinstance(self.expr, self.operator):
            return self.operator(self.func(first, *self.limits), self.func(second, *self.limits))
        return self

    @classmethod
    def identity(cls, self, **_):
        from sympy import Ones
        return Ones(*self.shape)

    @classmethod
    def is_identity(cls, self, **_):
        if self.shape:
            return self.is_Ones
        return self.is_One


class MatProduct(ExprWithIntLimits, MatrixExpr):
    r"""Represents unevaluated products of matrices.

    ``MatProduct`` represents a finite or infinite product, with the first
    argument being the general form of terms in the series, and the second
    argument being ``(dummy_variable, start, end)``, with ``dummy_variable``
    taking all integer values from ``start`` through ``end``. In accordance
    with long-standing mathematical convention, the end term is included in
    the product.

    Finite products
    ===============
    """

    is_complex = True
    operator = MatMul
    is_MatProduct = True
    
    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithIntLimits.__new__(cls, function, *symbols, **assumptions)

    @property
    def term(self):
        return self._args[0]

    function = term

    def _eval_is_zero(self):
        # a Product is zero only if its term is zero.
        function = self.expr
        from sympy import Range
        reps = {}
        for limit in self.limits[::-1]:
            x, *ab = limit
            if len(ab) == 1:
                domain, *_ = ab
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
                reps[x] = _x
            elif len(ab) == 2:
                a, b = ab
                if a.free_symbols & reps.keys():
                    a = a.subs(reps)
                    
                if b.free_symbols & reps.keys():
                    b = b.subs(reps)
                _x = x.copy(domain=Range(a, b + 1))
                function = function._subs(x, _x)
                reps[x] = _x
                
        return function.is_zero

    def doit(self, **hints):
        limit = self.limits[-1]
        x, a, b = limit
        dif = b - a
        if not dif.is_Integer:
            return self
        
        limits = self.limits[:-1]
        if limits:
            function = self.func(self.expr, *limits).doit(**hints)
        else:
            function = self.expr
        from sympy import sympify
        return MatMul(*[function._subs(x, sympify(i)) for i in range(dif)])    

    def _eval_adjoint(self):
        return self.func(self.expr.adjoint(), *self.limits)        

    def _eval_conjugate(self):
        return self.func(self.expr.conjugate(), *self.limits)

    def _eval_product(self, term, limits):
        from sympy.concrete.delta import deltaproduct, _has_simple_delta
        from sympy.concrete.summations import summation
        from sympy.functions import KroneckerDelta, RisingFactorial

        (k, a, n) = limits

        if k not in term.free_symbols:
            if (term - 1).is_zero:
                return S.One
            return term ** (n - a + 1)

        if a == n:
            return term.subs(k, a)

        if term.has(KroneckerDelta) and _has_simple_delta(term, limits[0]):
            return deltaproduct(term, limits)

        dif = n - a
        if dif.is_Integer:
            return Mul(*[term.subs(k, a + i) for i in range(dif + 1)])

        elif term.is_polynomial(k):
            poly = term.as_poly(k)

            A = B = Q = S.One

            all_roots = roots(poly)

            M = 0
            for r, m in all_roots.items():
                M += m
                A *= RisingFactorial(a - r, n - a + 1) ** m
                Q *= (n - r) ** m

            if M < poly.degree():
                arg = quo(poly, Q.as_poly(k))
                B = self.func(arg, limits).doit()

            return poly.LC() ** (n - a + 1) * A * B

        elif term.is_Add:
            factored = factor_terms(term, fraction=True)
            if factored.is_Mul:
                return self._eval_product(factored, limits)

        elif term.is_Mul:
            exclude, include = [], []

            for t in term.args:
                p = self._eval_product(t, limits)

                if p is not None:
                    exclude.append(p)
                else:
                    include.append(t)

            if not exclude:
                return None
            else:
                arg = term._new_rawargs(*include)
                A = Mul(*exclude)
                B = self.func(arg, limits).doit()
                return A * B

        elif term.is_Pow:
            if not term.base.has(k):
                s = summation(term.exp, limits)

                return term.base ** s
            elif not term.exp.has(k):
                p = self._eval_product(term.base, limits)

                if p is not None:
                    return p ** term.exp

        elif isinstance(term, Product):
            evaluated = term.doit()
            f = self._eval_product(evaluated, limits)
            if f is None:
                return self.func(evaluated, limits)
            else:
                return f

    def _eval_simplify(self, ratio, measure, rational, inverse):
        from sympy.simplify.simplify import product_simplify
        return product_simplify(self)

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            limits = self.limits
            function = self.expr
            for x, *ab in limits:
                if len(ab) != 2:
                    return None
                a, b = ab
                function = function._subs(x, a + b - 1 - x)
                
            return self.func(function.T, *limits)

    def is_convergent(self):
        r"""
        See docs of Sum.is_convergent() for explanation of convergence
        in SymPy.

        The infinite product:

        .. math::

            \prod_{1 \leq i < \infty} f(i)

        is defined by the sequence of partial products:

        .. math::

            \prod_{i=1}^{n} f(i) = f(1) f(2) \cdots f(n)

        as n increases without bound. The product converges to a non-zero
        value if and only if the sum:

        .. math::

            \sum_{1 \leq i < \infty} \log{f(n)}

        converges.

        Examples
        ========

        >>> from sympy import Interval, S, Product, Symbol, cos, pi, exp, oo
        >>> n = Symbol('n', integer=True)
        >>> Product(n/(n + 1), (n, 1, oo)).is_convergent()
        False
        >>> Product(1/n**2, (n, 1, oo)).is_convergent()
        False
        >>> Product(cos(pi/n), (n, 1, oo)).is_convergent()
        True
        >>> Product(exp(-n**2), (n, 1, oo)).is_convergent()
        False

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Infinite_product
        """
        from sympy.concrete.summations import Sum

        sequence_term = self.expr
        log_sum = log(sequence_term)
        lim = self.limits
        try:
            is_conv = Sum(log_sum, *lim).is_convergent()
        except NotImplementedError:
            if Sum(sequence_term - 1, *lim).is_absolutely_convergent() is S.true:
                return S.true
            raise NotImplementedError("The algorithm to find the product convergence of %s "
                                        "is not yet implemented" % (sequence_term))
        return is_conv

    def reverse_order(expr, *indices):
        """
        Reverse the order of a limit in a Product.

        Usage
        =====

        ``reverse_order(expr, *indices)`` reverses some limits in the expression
        ``expr`` which can be either a ``Sum`` or a ``Product``. The selectors in
        the argument ``indices`` specify some indices whose limits get reversed.
        These selectors are either variable names or numerical indices counted
        starting from the inner-most limit tuple.

        Examples
        ========

        >>> from sympy import Product, simplify, RisingFactorial, gamma, Sum
        >>> from sympy.abc import x, y, a, b, c, d
        >>> P = Product(x, (x, a, b))
        >>> Pr = P.reverse_order(x)
        >>> Pr
        Product(1/x, (x, b + 1, a - 1))
        >>> Pr = Pr.doit()
        >>> Pr
        1/RisingFactorial(b + 1, a - b - 1)
        >>> simplify(Pr)
        gamma(b + 1)/gamma(a)
        >>> P = P.doit()
        >>> P
        RisingFactorial(a, -a + b + 1)
        >>> simplify(P)
        gamma(b + 1)/gamma(a)

        While one should prefer variable names when specifying which limits
        to reverse, the index counting notation comes in handy in case there
        are several symbols with the same name.

        >>> S = Sum(x*y, (x, a, b), (y, c, d))
        >>> S
        Sum(x*y, (x, a, b), (y, c, d))
        >>> S0 = S.reverse_order(0)
        >>> S0
        Sum(-x*y, (x, b + 1, a - 1), (y, c, d))
        >>> S1 = S0.reverse_order(1)
        >>> S1
        Sum(x*y, (x, b + 1, a - 1), (y, d + 1, c - 1))

        Of course we can mix both notations:

        >>> Sum(x*y, (x, a, b), (y, 2, 5)).reverse_order(x, 1)
        Sum(x*y, (x, b + 1, a - 1), (y, 6, 1))
        >>> Sum(x*y, (x, a, b), (y, 2, 5)).reverse_order(y, x)
        Sum(x*y, (x, b + 1, a - 1), (y, 6, 1))

        See Also
        ========

        index, reorder_limit, reorder

        References
        ==========

        .. [1] Michael Karr, "Summation in Finite Terms", Journal of the ACM,
               Volume 28 Issue 2, April 1981, Pages 305-350
               http://dl.acm.org/citation.cfm?doid=322248.322255
        """
        l_indices = list(indices)

        for i, indx in enumerate(l_indices):
            if not isinstance(indx, int):
                l_indices[i] = expr.index(indx)

        e = 1
        limits = []
        for i, limit in enumerate(expr.limits):
            l = limit
            if i in l_indices:
                e = -e
                l = (limit[0], limit[2] + 1, limit[1] - 1)
            limits.append(l)

        return Product(expr.expr ** e, *limits)

    def simplify(self, deep=False, **_):
        if len(self.limits) > 1:
            limit = self.limits[-1]
            if len(limit) == 3:
                function = self.func(self.expr, *self.limits[:-1])
                x, a, b = limit
                if not function._has(x):
                    return function ^ (b - a)
                
                if a == b - 1:
                    return function._subs(x, a).simplify(deep=deep)
                if a >= b:
                    return S.One
            return self
        
        limit = self.limits[0]
        if len(limit) == 2:
            x, domain = limit
            if domain.is_FiniteSet and len(domain) == 1:
                return self.finite_aggregate(x, domain)
            if not self.expr._has(x):
                return self.expr ^ abs(domain)
                            
        elif len(limit) == 3:
            x, a, b = limit
            if not self.expr._has(x):
                return self.expr ^ (b - a)
            
            if a == b - 1:
                return self.expr._subs(x, a)
            from sympy import Identity
            if a >= b:
                return Identity(self.shape[0])
        else:
            x, *_ = limit
        function = self.expr
        independent, dependent = function.as_independent(x, as_Add=False)
        if independent == S.One:
            return self

        if dependent == S.One:
            if len(limit) > 1:
                return self.expr ^ (b - a)
            else:
                return self.expr ^ x.dimension
        if len(limit) > 1:
            return self.func(dependent, limit).doit() @ (independent ^ (b - a))
        else:
            return self.func(dependent, limit).doit() @ (independent ^ x.dimension)

    def _sympystr(self, p):
        limits = ','.join([':'.join([p._print(arg) for arg in limit]) for limit in self.limits])
        return 'MatProduct[%s](%s)' % (limits, p._print(self.expr))

    def _lean(self, p):
        limits = ','.join([':'.join([p._print(arg) for arg in limit]) for limit in self.limits])
        return '\N{N-ARY PRODUCT} %s, %s' % (limits, p._print(self.expr))

    latex_name_of_operator = 'prod'

    def try_absorb_forward(self, expr):
        if len(self.limits) == 1:
            i, *ab = self.limits[0]
            if len(ab) == 2 and expr:
                a, b = ab
                if self.expr.subs(i, a - 1) == expr:
                    return self.func(self.expr, (i, a - 1 , b))

    def try_absorb_backward(self, expr):
        if len(self.limits) == 1:
            i, *ab = self.limits[0]
            if len(ab) == 2 and expr:
                a, b = ab
                if self.expr.subs(i, b) == expr:
                    return self.func(self.expr, (i, a, b + 1))

    def _entry(self, i, j=None):
        if isinstance(i, Tuple):
            start, stop, step = i.slice_args
            if start == 0:
                if stop == self.shape[0]:
                    if j is not None:
                        if isinstance(j, Tuple):
                            start, stop, step = j.slice_args
                            if start == 0 and stop == self.shape[1]:
                                return self
                            
                        if len(self.limits) > 1:
                            return
                        limit = self.limits[0]
                        x, a, b = limit
                        if a < b:
                            return self.func[x:a:b - 1](self.expr) @ self.expr._subs(x, b - 1)[:, j]
                        else:
                            return

    def _subs(self, old, new, **hints):
        intersect = new.free_symbols & self.variables_set - old.free_symbols
        if intersect:
            this = self
            excludes = self.variables_set | new.free_symbols
            for var in intersect:
                _var = self.generate_var(excludes, integer=True)
                this = this.limits_subs(var, _var)
                excludes.add(_var) 
            _this = this._subs(old, new)
            if _this == this:
                return self
            return _this
        
        from sympy.core.basic import _aresame
        if self == old or _aresame(self, old) or self.dummy_eq(old):
            return new
                
        if not self._has(old):
            return self
        
        if len(self.limits) == 1:
            limit = self.limits[0]
            x, *ab = limit

            if ab:
                if len(ab) == 1:
                    domain = ab[0]
                    if old.has(x):
                        if domain.is_set:
                            _domain = domain._subs(old, new)
                            if _domain != domain:
                                return self.func(self.expr, (x, _domain)).simplify()
                    else:
                        _domain = domain._subs(old, new)
                        function = self.expr._subs(old, new)
                        if _domain != domain or function != self.expr:
                            return self.func(function, (x, _domain)).simplify()

                    return self

                a, b = ab

            if old.is_Sliced and len(ab) == 2:
                from sympy import Range
                _x = x.copy(domain=Range(*ab))
                function = self.expr.subs(x, _x)
                _function = function.subs(old, new)
                if _function != function:
                    function = _function.subs(_x, x)
                    return self.func(function, *self.limits)

            p = old.as_poly(x)

            if p is None or p.degree() != 1:
                function = self.expr._subs(old, new).simplify()

                if ab:
                    return self.func(function, (x, a.subs(old, new), b.subs(old, new))).simplify()

                if x.is_Sliced:
                    x = x.subs(old, new)
                return self.func(function, (x,))

            if new.has(x):
                diff = old - new
                if old != x:
                    if diff.has(x):
                        return self

                    alpha = p.coeff_monomial(x)
                    diff /= alpha

                function = self.expr.subs(x, x - diff)
                if ab:
                    return self.func(function, (x, a + diff, b + diff))
                else:
                    return self.func(function, (x,))
            from sympy import solve
            if old != x:
                sol = solve(old - new, x)
                if len(sol) != 1:
                    return self
                new = sol[0]

            _x = new.free_symbols - old.free_symbols

            if len(_x) != 1:
                return self
            _x, *_ = _x

            function = self.expr.subs(x, new)

            if ab:
                a = solve(new - a, _x)
                b = solve(new - b, _x)
                if len(a) != 1 or len(b) != 1:
                    return self
                a, b = a[0], b[0]

                p = new.as_poly(_x)
                alpha = p.coeff_monomial(_x)
                if alpha > 0:
                    return self.func(function, (_x, a, b))
                elif alpha < 0:
                    return self.func(function, (_x, b, a))
                else:
                    return self

            return self.func(function, (_x))

        elif len(self.limits) == 0:
            function = self.expr.subs(old, new)

            return self.func(function, *self.limits)
        else:
            index = -1
            for i, limit in enumerate(self.limits):
                x, *ab = limit
                if ab:
                    a, b = ab

                p = old.as_poly(x)
                if p is None:
                    continue
                if p.degree() != 1:
                    continue
                index = i

                if new.has(x):
                    diff = old - new
                    if old != x:
                        if diff.has(x):
                            return self

                        alpha = p.coeff_monomial(x)
                        diff /= alpha

                    function = self.expr.subs(x, x - diff)
                    if ab:
                        limit = (x, a + diff, b + diff)
                break

            if index < 0:
                return self.func(self.expr._subs(old, new), *self.limits)

            limits = [*self.limits]
            limits[index] = limit
            return self.func(function, *limits)

        return self

    @classmethod
    def identity(cls, self, **_):
        from sympy import Identity
        return Identity(self.shape[-1])

    @classmethod
    def is_identity(cls, self, **_):
        return self.is_Identity


def product(*args, **kwargs):
    r"""
    Compute the product.

    The notation for symbols is similar to the notation used in Sum or
    Integral. product(f, (i, a, b)) computes the product of f with
    respect to i from a to b, i.e.,

    ::

                                     b
                                   _____
        product(f(n), (i, a, b)) = |   | f(n)
                                   |   |
                                   i = a

    If it cannot compute the product, it returns an unevaluated Product object.
    Repeated products can be computed by introducing additional symbols tuples::

    >>> from sympy import product, symbols
    >>> i, n, m, k = symbols('i n m k', integer=True)

    >>> product(i, (i, 1, k))
    factorial(k)
    >>> product(m, (i, 1, k))
    m**k
    >>> product(i, (i, 1, k), (k, 1, n))
    Product(factorial(k), (k, 1, n))

    """

    prod = Product(*args, **kwargs)

    if isinstance(prod, Product):
        return prod.doit(deep=False)
    else:
        return prod


Mul.identity = S.One
