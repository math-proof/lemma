from sympy.core.add import Add
from sympy.core.compatibility import is_sequence
from sympy.core.containers import Tuple
from sympy.core.expr import Expr
from sympy.core.mul import Mul
from sympy.core.relational import Relational
from sympy.core.singleton import S
from sympy.core.symbol import Symbol, Dummy, Wild
from sympy.core.sympify import sympify
from sympy.functions.elementary.piecewise import piecewise_fold, Piecewise
from sympy.logic.boolalg import BooleanFunction, Boolean, And, Or
    
from sympy.matrices import Matrix
from sympy.tensor.indexed import Idx, Indexed
from sympy.sets.sets import FiniteSet
from sympy.sets.fancysets import Range
from sympy.utilities import flatten
from sympy.utilities.iterables import sift, postorder_traversal
from sympy.functions.elementary.miscellaneous import Min, Max
from sympy.matrices.expressions.blockmatrix import BlockMatrix
from sympy.core.cache import cacheit
from collections import defaultdict, OrderedDict


def _common_new(cls, expr, *symbols, **assumptions):
    """Return either a special return value or the tuple,
    (expr, limits, orientation). This code is common to
    both ExprWithLimits and AddWithLimits."""
    expr = sympify(expr)

    if expr is S.NaN:
        return S.NaN

    if symbols:
        limits, orientation = _process_limits(*symbols)
        for i, li in enumerate(limits):
            if len(li) == 4:
                expr = expr.subs(li[0], li[-1])
                limits[i] = tuple(li[:-1])
                
            elif len(li) == 3:
                oldsymbol, a, b = li
# added here to remove the domain of this variable!
                if isinstance(oldsymbol, Symbol) and oldsymbol.is_bounded:
                    newsymbol = oldsymbol.unbounded
                    expr = expr._subs(oldsymbol, newsymbol)
                    limits[i] = Tuple(newsymbol, *li[1:])
                else:
                    if oldsymbol.is_integer and a == b:
                        expr = cls.identity(expr)
            elif len(li) == 2:
                x, domain = li
                if domain.is_EmptySet or domain.is_BooleanFalse:
                    expr = cls.identity(expr)
                elif domain.is_Interval and cls.is_Integral:
                    if domain.start <= domain.stop:
                        limits[i] = Tuple(x, domain.start, domain.stop)
                elif domain.is_BinaryCondition:
                    if hit := cls.process_binary_condition(li, expr):
                        expr, li = hit
                        limits[i] = Tuple(*li)

    else:
        limits, orientation = [], 1

    # unnest any nested calls
    if assumptions.get('evaluate', True):
        while cls == type(expr):
            limits = list(expr.limits) + limits
            expr = expr.expr

    # Any embedded piecewise functions need to be brought out to the
    # top level. We only fold Piecewise that contain the integration
    # variable.
    reps = {}
    symbols_of_integration = set([i[0] for i in limits])
    for p in expr.atoms(Piecewise):
        if not p.has(*symbols_of_integration):
            reps[p] = Dummy(**p.dtype.dict)
    # mask off those that don't
    expr = expr.xreplace(reps)
    # do the fold
    expr = piecewise_fold(expr)
    # remove the masking
    expr = expr.xreplace({v: k for k, v in reps.items()})

    return expr, limits, orientation


def _process_limits(*symbols):
    """Process the list of symbols and convert them to canonical limits,
    storing them as Tuple(symbol, lower, upper). The orientation of
    the function is also returned when the upper limit is missing
    so (x, 1, None) becomes (x, None, 1) and the orientation is changed.
    """
    limits = []
    orientation = 1
    for V in symbols:
        if isinstance(V, (Relational, BooleanFunction)):
            variable = V.atoms(Symbol).pop()
            V = (variable, V.as_set())

        if isinstance(V, Symbol) or getattr(V, '_diff_wrt', False):
            if isinstance(V, Idx):
                if V.lower is None or V.upper is None:
                    limits.append(Tuple(V))
                else:
                    limits.append(Tuple(V, V.lower, V.upper))
            else:
                limits.append(Tuple(V))
            continue
        elif is_sequence(V, Tuple):
            if len(V) >= 2:
                if isinstance(V[1], Boolean):
                    if V[1]:
                        x, _, *ab = V
                        if ab:
                            domain = ab[0]
                            if domain.is_Range:
                                start = domain.start
                                stop = domain.stop
                                limits.append(Tuple(x, start, stop))
                            else:
                                limits.append(Tuple(x, domain))
                        else:
                            limits.append(Tuple(x))
                    else:
                        limits.append(Tuple(*V))
                    continue
                if len(V) == 2:
                    if isinstance(V[1], Range) and V[1].step.is_One:
                        V = V[0], V[1].start, V[1].stop
                    elif isinstance(V[1], set):
                        V = V[0], FiniteSet(*V[1])
            if not isinstance(V, list):
                V = [*V]  # a list of sympified elements
            if isinstance(V[0], (Symbol, Idx)) or getattr(V[0], '_diff_wrt', False):
                newsymbol = V[0]
                if len(V) == 2:
                    if V[1].is_Interval:  # 2 -> 3
                        if newsymbol.is_integer:
                            rgn = V[1].copy(integer=True)
                            V[1:] = rgn.start, rgn.stop
                        else:
                            start, stop = V[1].args
                            if start <= stop:
                                V[1:] = start, stop
                                
                    elif V[1].is_Range and V[1].step.is_One:  # 2 -> 3
                        V[1:] = V[1].start, V[1].stop
                        if not newsymbol.is_integer:
                            symbolModified = Symbol(newsymbol.name, integer=True)
                            raise
                            function._subs(newsymbol, symbolModified)
                            V[0] = symbolModified
                            
                elif len(V) == 3:
                    # general case
                    if V[2] is None and not V[1] is None:
                        orientation *= -1
                        
                    V = [newsymbol] + [i for i in V[1:] if i is not None]

                if not isinstance(newsymbol, Idx) or len(V) == 3:
                    if len(V) == 4:
                        limits.append(Tuple(*V))
                        continue
                    if len(V) == 3:
                        if isinstance(newsymbol, Idx):
                            # Idx represents an integer which may have
                            # specified values it can take on; if it is
                            # given such a value, an error is raised here
                            # if the summation would try to give it a larger
                            # or smaller value than permitted. None and Symbolic
                            # values will not raise an error.
                            lo, hi = newsymbol.lower, newsymbol.upper
                            try:
                                if lo is not None and not bool(V[1] >= lo):
                                    raise ValueError("Summation will set Idx value too low.")
                            except TypeError:
                                pass
                            try:
                                if hi is not None and not bool(V[2] <= hi):
                                    raise ValueError("Summation will set Idx value too high.")
                            except TypeError:
                                pass
                            
                        limits.append(Tuple(*V))
                        continue
                    if len(V) == 1 or (len(V) == 2 and V[1] is None):
                        limits.append(Tuple(newsymbol))
                        continue
                    elif len(V) == 2:
                        limits.append(Tuple(newsymbol, V[1]))
                        continue

        raise ValueError('Invalid limits given: %s' % str(symbols))

    return limits, orientation


class ExprWithLimits(Expr):
    __slots__ = ['is_commutative']

    def _eval_is_extended_integer(self):
        return self.expr.is_extended_integer

    def _eval_is_random(self):
        if self.expr.is_random:
            return True

        for x, *ab in self.limits:
            for v in ab:
                if v.is_random:
                    return True

    def yield_random_symbols(self):
        limits = self.limits
        expr = self.expr
        for v in expr.yield_random_symbols():
            if v.is_Indexed or v.is_Sliced or v.is_SlicedIndexed:
                if v_expanded := v.expand_indices(limits, expr):
                    v = v_expanded
            yield v

        for x, *ab in limits:
            for v in ab:
                yield from v.yield_random_symbols()
    
    def yield_effective_variable(self, variable):
        limits = self.limits
        expr = self.expr
        for v in expr.yield_effective_variable(variable):
            if v.is_Indexed or v.is_Sliced or v.is_SlicedIndexed:
                if v_expanded := v.expand_indices(limits, expr):
                    if v_expanded._has(variable):
                        v = v_expanded
                    else:
                        continue
            yield v

        for x, *ab in limits:
            for v in ab:
                yield from v.yield_effective_variable(variable)

    def finite_aggregate(self, x, s):
        k, *_ = s.args
        expr = self.expr._subs(x, k)
        return expr.simplify()

    def limits_intersect(self, expr, clue=None):
        return limits_intersect(self.limits, expr.limits, clue=clue)

    def limits_union(self, expr):
        return limits_union(self.limits, expr.limits)

# precondition, self and other are structurally equal!
    def _dummy_eq(self, other):
        _self = other
        for (x, *ab), (_x, *_ab) in zip(other.limits, self.limits):
            if x != _x:
                if not ab and x.domain != _x.domain:
                    return False

                if _x in _self.variables:
                    return False

                _self = _self.limits_subs(x, _x)
                if not _self.is_ExprWithLimits:
                    return False
                    
        return _self.limits == self.limits and _self.expr._dummy_eq(self.expr)

    @property
    def limits_dict(self):
        return limits_dict(self.limits)

    @property
    def limits_cond(self):
        return limits_cond(self.limits)

    def limits_update(self, *args):
        return limits_update(self.limits, *args)

    def limits_delete(self, dic):
        return limits_delete(self.limits, dic)

    def limits_common(self, eq, is_or=False):
        return limits_common(self.limits, eq.limits, is_or)

    def limits_in_context(self, has_args=None, parent=None):
        if has_args:
            return [*self.limits]
        
        limits = []
        for limit in self.limits:
            x, *ab = limit
            if not ab and x.is_integer:
                domain = self.expr.domain_defined(x)
                limit = (x, domain)
            limits.append(limit)
            
        limits.reverse()
        return limits

    @property
    def dtype(self):
        return self.expr.dtype

    @classmethod
    def process_binary_condition(cls, sym, expr):
        x, domain = sym
        hit = False
        if domain.lhs == x:
            if domain.is_GreaterEqual:
                if x.is_integer:
                    sym = (x, domain.rhs, S.Infinity)
                    hit = True
                    
            elif domain.is_Less:
                if x.is_integer:
                    if x.is_nonnegative:
                        _x = x.unbounded
                        sym = _x, 0, domain.rhs
                        expr = expr._subs(x, _x)
                    else:
                        sym = (x, -S.Infinity, domain.rhs)
                    hit = True
                elif x.is_real:
                    if x.is_positive:
                        _x = x.unbounded
                        sym = _x, 0, domain.rhs
                        expr = expr._subs(x, _x)
                    else:
                        sym = (x, -S.Infinity, domain.rhs)

                    hit = True
                        
            elif domain.is_Greater:
                if x.is_integer:
                    if domain.rhs.is_integer:
                        sym = (x, domain.rhs + 1, S.Infinity)
                        hit = True
                elif x.is_real:
                    sym = (x, domain.rhs, S.Infinity)
                    hit = True
                    
            elif domain.is_Element:
                domain = domain.rhs
                args = [domain]
                if x.is_integer:
                    if domain.is_Range:
                        args = domain.args
                else:
                    if domain.is_Interval and domain.is_open:
                        args = domain.args
                sym = x, *args
                hit = True
                
            elif domain.is_Equal:
                sym = (x, FiniteSet(domain.rhs))
                hit = True

        elif domain.rhs == x:
            if domain.is_LessEqual:  # lhs <= x
                if x.is_integer:
                    sym = (x, domain.lhs, S.Infinity)
                    hit = True
            elif domain.is_Greater:  # lhs > x
                if x.is_integer:
                    if x.is_nonnegative:
                        _x = x.unbounded
                        sym = _x, 0, domain.lhs
                        expr = expr._subs(x, _x)
                    else: 
                        sym = (x, -S.Infinity, domain.lhs)
                    hit = True
                elif x.is_real:
                    if x.is_positive:
                        _x = x.unbounded
                        sym = _x, 0, domain.lhs
                        expr = expr._subs(x, _x)
                    else: 
                        sym = (x, -S.Infinity, domain.lhs)
                    hit = True
            elif domain.is_GreaterEqual:  # lhs >= x
                if x.is_integer:
                    ...
                elif x.is_real:
                    if cls.is_Integral:
                        if x.is_nonnegative or x.is_positive:
                            _x = x.unbounded
                            sym = (_x, 0, domain.lhs)
                            expr = expr._subs(x, _x)
                        else:
                            sym = (x, -S.Infinity, domain.lhs)
                        hit = True
            elif domain.is_Equal:
                sym = (x, FiniteSet(domain.lhs))
                hit = True
        
        if hit:
            return expr, sym

    def __new__(cls, expr, *symbols, **assumptions): 
        limits = []
        symbols = [*symbols]
        for i in range(len(symbols) - 1, -1, -1):
            sym = symbols[i]
            if isinstance(sym, tuple):
                sym = Tuple(*sym)
            
            if isinstance(sym, Tuple):
                x, *ab = sym
                if x.is_symbol:
                    if len(sym) == 2:
                        domain, = ab
                        if domain.is_set:
                            assert x.type in domain.etype or domain.etype in x.type, "domain.etype = %s\n, x.type = %s" % (domain.etype, x.type)
                            if x.is_Symbol and x.is_bounded:
                                domain &= x.domain_bounded
                                _x = x.unbounded
                                sym = _x, domain
                                expr, symbols = cls.expr_subs(expr, symbols, x, _x, i)
                                x = _x

                            if domain.is_Range and domain.step.is_One:
                                if domain.is_UniversalSet:
                                    sym = (x,)
                                else:
                                    sym = (x, domain.start, domain.stop)
                            elif domain.is_Interval:
                                if domain.is_UniversalSet:
                                    sym = (x,)
                                elif domain.left_open and domain.right_open:
                                    sym = (x, domain.start, domain.stop)
                                    
                            elif domain.is_ConditionSet and domain.variable == x:
                                if domain.base_set.is_UniversalSet:
                                    sym = (x, domain.condition)
                                else:
                                    sym = (x, domain.condition, domain.base_set)
                            elif domain.is_empty:
                                return cls.identity(expr)

                        elif domain.is_bool:
                            if domain.is_BinaryCondition:
                                if hit := cls.process_binary_condition(sym, expr):
                                    expr, sym = hit
                            elif domain:
                                sym = x,
                            elif domain.is_BooleanFalse:
                                return cls.identity(expr)

                    elif len(sym) == 3:
                        a, b = ab
                        if x.is_Symbol and x.is_bounded and not a.is_bool:
                            _x = x.unbounded
                            sym = _x, a, b
                            expr, symbols = cls.expr_subs(expr, symbols, x, _x, i)
                        
                        if a.is_bool:
                            if a:
                                if b.is_Range and x.is_integer:
                                    if b.is_UniversalSet:
                                        sym = (x,)
                                    else:
                                        sym = (x, b.start, b.stop)
                                else:
                                    sym = (x, b)
                            elif b.is_UniversalSet:
                                sym = (x, a)
                                
                            elif a.is_Element and a.lhs == x:
                                domain = b & a.rhs
                                if domain.is_Range and domain.step.is_One:
                                    sym = (x, domain.start, domain.stop)
                                else:
                                    sym = (x, domain)
                            
                        elif x.type.is_DtypeInteger and not b.is_set:
                            if a == b - 1:
                                expr, symbols = cls.expr_subs(expr, symbols, x, a, i)
                                continue
                            elif a == b:
                                return cls.identity(expr, **assumptions)
                    
                    limits.append(Tuple(*sym))
                else:
                    if ab:
                        if x.is_BlockMatrix:
                            flat_list = x.args
                        else:
                            flat_list = x._args
                            
                        for arg in flat_list[:0:-1]:
                            limits.append(Tuple(arg,))
                        limits.append(Tuple(flat_list[0], *ab))
                    else:
                        for arg in x._args[::-1]:
                            limits.append(Tuple(arg,))
                    
            else:
                limits.append(Tuple(sym,))
                
        limits.reverse()
        return cls.unnest(expr, limits, symbols, **assumptions)

    @classmethod
    def expr_subs(cls, expr, symbols, old, new, i):
        expr = expr._subs(old, new)
        for j in range(i - 1, -1, -1):
            x, *ab = symbols[j]
            if x == old:
                symbols[j] = (x, *(sympify(e)._subs(old, new) for e in ab))
                break
            else:
                symbols[j] = tuple(sympify(e)._subs(old, new) for e in symbols[j])
                
        return expr, symbols
        
    @classmethod
    def unnest(cls, expr, limits, symbols, **assumptions):
    # unnest any nested calls
        while cls == type(expr):
            limits = list(expr.limits) + limits
            expr = expr.expr

        if not limits and symbols or cls.is_identity(expr):
            return expr.copy(**assumptions)

        return Expr.__new__(cls, expr, *limits, **assumptions)

    @property
    def expr(self):
        """Return the expression applied across limits.

        Examples
        ========

        >>> from sympy import Integral
        >>> from sympy.abc import x
        >>> Integral(x**2, (x,)).expr
        x**2

        See Also
        ========

        limits, variables, free_symbols
        """
        return self._args[0]
    
    @property
    def limits(self):
        """Return the limits of expression.

        Examples
        ========

        >>> from sympy import Integral
        >>> from sympy.abc import x, i
        >>> Integral(x**i, (i, 1, 3)).limits
        ((i, 1, 3),)

        See Also
        ========

        function, variables, free_symbols
        """
        return self._args[1:]

    @property
    def _limits(self):
        return self.expr._limits + self.limits

    @property
    def variables(self):
        """Return a list of the limit variables.

        >>> from sympy import Sum
        >>> from sympy.abc import x, i
        >>> Sum(x**i, (i, 1, 3)).variables
        [i]

        See Also
        ========

        function, limits, free_symbols
        as_dummy : Rename dummy variables
        transform : Perform mapping on the dummy variable
        """
        return tuple(l[0] for l in self.limits)

    @property
    def variable(self):
        return self.limits[0][0]

    @property
    def variables_set(self):
        return {l[0] for l in self.limits}

    @property
    def bound_symbols(self):
        """Return only variables that are dummy variables.

        Examples
        ========

        >>> from sympy import Integral
        >>> from sympy.abc import x, i, j, k
        >>> Integral(x**i, (i, 1, 3), (j, 2), k).bound_symbols
        [i, j]

        See Also
        ========

        function, limits, free_symbols
        as_dummy : Rename dummy variables
        transform : Perform mapping on the dummy variable
        """
        return [l[0] for l in self.limits if len(l) != 1]

    @cacheit
    def _eval_free_symbols(self):
        """
        This method returns the symbols in the object, excluding those
        that take on a specific value (i.e. the dummy symbols).

        Examples
        ========

        >>> from sympy import Sum
        >>> from sympy.abc import x, y
        >>> Sum(x, (x, y, 1)).free_symbols
        {y}
        """
        # don't test for any special values -- nominal free symbols
        # should be returned, e.g. don't return set() if the
        # function is zero -- treat it like an unevaluated expression.
        expr, limits = self.expr, self.limits
        isyms = {*expr.free_symbols}
        for xab in limits:
            # take out the target symbol
            x, *ab = xab
            if x in isyms:
                isyms.remove(x)
            # add in the new symbols
            isyms -= {var for var in isyms if var._has(x)}
            
            for c in ab:
                symbols = c.free_symbols
                if c.is_bool:
                    symbols = symbols - {var for var in symbols if var._has(x)}
                
                isyms.update(symbols)
        return isyms

    @property
    def is_number(self):
        """Return True if the Sum has no free symbols, else False."""
        if self.free_symbols:
            return False
        
        from sympy.core.function import AppliedUndef
        for f in self.finditer(AppliedUndef):
            return False

        return True

    def _eval_interval(self, x, a, b):
        limits = [(i if i[0] != x else (x, a, b)) for i in self.limits]
        integrand = self.expr
        return self.func(integrand, *limits)

    def _eval_subs(self, old, new, **hints):
        """
        Perform substitutions over non-dummy variables
        of an expression with limits.  Also, can be used
        to specify point-evaluation of an abstract antiderivative.

        Examples
        ========

        >>> from sympy import Sum, oo
        >>> from sympy.abc import s, n
        >>> Sum(1/n**s, (n, 1, oo)).subs(s, 2)
        Sum(n**(-2), (n, 1, oo))

        >>> from sympy import Integral
        >>> from sympy.abc import x, a
        >>> Integral(a*x**2, x).subs(x, 4)
        Integral(a*x**2, (x, 4))

        See Also
        ========

        variables : Lists the integration variables
        transform : Perform mapping on the dummy variable for integrals
        change_index : Perform mapping on the sum and product dummy variables

        """
        from sympy.core.function import AppliedUndef, UndefinedFunction
        func, limits = self.expr, list(self.limits)

        # If one of the expressions we are replacing is used as a func index
        # one of two things happens.
        #   - the old variable first appears as a free variable
        #     so we perform all free substitutions before it becomes
        #     a func index.
        #   - the old variable first appears as a func index, in
        #     which case we ignore.  See change_index.

        # Reorder limits to match standard mathematical practice for scoping
        limits.reverse()

        if not isinstance(old, Symbol) or \
                old.free_symbols.intersection(self.free_symbols):
            sub_into_func = True
            for i, xab in enumerate(limits):
                if 1 == len(xab) and old == xab[0]:
                    if new._diff_wrt:
                        xab = (new,)
                    else:
                        xab = (old, old)
                limits[i] = Tuple(xab[0], *[l._subs(old, new) for l in xab[1:]])
                if self.func.__name__ in ('Sum', 'Product', 'Integral'):
                    if len(xab[0].free_symbols.intersection(old.free_symbols)) != 0:
                        sub_into_func = False
                        break

            if isinstance(old, AppliedUndef) or isinstance(old, UndefinedFunction):
                sy2 = set(self.variables).intersection(set(new.atoms(Symbol)))
                sy1 = set(self.variables).intersection(set(old.args))
                if not sy2.issubset(sy1):
                    raise ValueError(
                        "substitution can not create dummy dependencies")
                sub_into_func = True
            if sub_into_func:
                func = func.subs(old, new)
        else:
            # old is a Symbol and a dummy variable of some limit
            for i, xab in enumerate(limits):
                if len(xab) == 3:
                    limits[i] = Tuple(xab[0], *[l._subs(old, new) for l in xab[1:]])
                    if old == xab[0]:
                        break
        # simplify redundant limits (x, x)  to (x, )
        for i, xab in enumerate(limits):
            if len(xab) == 2 and (xab[0] - xab[1]).is_zero:
                limits[i] = Tuple(xab[0],)

        # Reorder limits back to representation-form
        limits.reverse()

        return self.func(func, *limits)
    
    def _subs_limits(self, x, domain, new, simplify=True):

        def subs(expr, x, domain, new):
            if x.is_Sliced:
                indexed_set = x.detect_indexed(expr)
                if indexed_set:
                    reps = {}
                    _function = expr
                    for indexed in indexed_set:
                        indices = indexed.indices
                        for index in indices: 
                            if index.is_symbol:
                                indexDomain = index.domain
                                _indexDomain = self.domain_defined(index)
                                if _indexDomain != indexDomain:
                                    _index = index.copy(domain=_indexDomain)
                                    _function = _function._subs(index, _index)
                                    reps[index] = _index
                                       
                    _function = _function._subs(x, new)
                    
                    if reps:
                        for index, _index in reps.items():
                            _function = _function._subs(_index, index)
                else:
                    _function = expr._subs(x, new)
            else:
                _function = expr._subs(x, new)
                
            if _function == expr:
                if not expr._has(x):
                    ...
                else:
                    return self
            expr = _function
            
            kwargs = {}
            if self.is_Boolean:
                kwargs['equivalent'] = self

            index = self.variables.index(x)
            limits = [*self.limits]
            if 'domain' in new._assumptions:
                if len(domain) == 2:
                    assert new.domain == x.range(*domain)
                elif domain:
                    dom = domain[0]
                    if not dom.is_set:
                        dom = new.domain_conditioned(dom)
                    assert new.domain == dom
                limits[index] = (new,)
            elif len(domain) == 1:
                domain = domain[0]
                if domain.is_bool:
                    domain = domain._subs(x, new)
                limits[index] = (new, domain)
            elif not domain:
                if 'domain' in x._assumptions:
                    domain = x.domain_assumed
                    limits[index] = (new, domain)
                else:
                    limits[index] = (new,)
            else:
                limits[index] = new, *domain
                
            for i in range(index):
                v, *domain = limits[i]
                domain = [dom._subs(x, new) for dom in domain]
                limits[i] = (v, *domain)

            this = self.func(expr, *limits, **kwargs)
            return this.simplify() if simplify else this

        if self.expr.is_ExprWithLimits and new in self.expr.variables_set:
            if self.expr.is_Exists:
                return self
            y = self.expr.generate_var(self.expr.variables_set, **new.type.dict)
            assert new != y
            expr = self.expr.limits_subs(new, y)
            if expr == self.expr:
                return self
            this = subs(expr, x, domain, new)
 
            if this.is_ExprWithLimits:
                if this.expr.is_ExprWithLimits and y in this.expr.variables_set:
                    expr = this.expr.limits_subs(y, x)
                else:
                    expr = this.expr
     
                this = this.func(expr, *this.limits)
                
            if this.is_Boolean:
                this.equivalent = self
            return this
        return subs(self.expr, x, domain, new)

    def limits_subs(self, old, new, simplify=True, **kwargs):
        from sympy.solvers import solve
        if len(self.limits) == 1:
            limit = self.limits[0]
            x, *domain = limit

            if old == x:
                if self.expr._has(new):
                    if x.is_Indexed and old.is_Indexed and new.is_Indexed:                         
                        v = self.generate_var({x, old, new}, dtype=new.dtype)
                        self_tmp = self.limits_subs(old, v)
                        if self_tmp != self:
                            self_tmp = self_tmp.limits_subs(v, new)
                            if self_tmp != self:
                                return self_tmp
                    return self
                
                if not domain: 
                    if new._has(x):
                        p = new.as_poly(x)
                        if p is None or p.degree() != 1:
                            return self
                        alpha = p.coeff_monomial(x)
                        if alpha == 1:
                            diff = new - x
                            a, b = x.domain.min() - diff, x.domain.max() - diff
                            self = self.func(self.expr._subs(old, new), (x, a, b))
                            return self.simplify() if simplify else self
                        elif alpha == -1:
                            return self
                        else:
                            return self
                    else:
                        domain_assumed = new.domain_assumed
                        if domain_assumed: 
                            assert domain_assumed == x.domain
                            limit = (new,)
                        else:
                            domain = x.domain
                            if domain.is_UniversalSet:
                                limit = (new,)
                            else:
                                limit = (new, domain)
                                
                        self = self.func(self.expr._subs(old, new), limit)
                        return self.simplify() if simplify else self
                if not new._has(x):
                    return self._subs_limits(x, domain, new, simplify=simplify)

            if len(domain) == 2:
                a, b = domain

            p = old.as_poly(x)

            if p is None or p.degree() != 1:
                if x.is_Sliced:
                    x = x.subs(old, new)
                    self = self.func(self.expr.subs(old, new), (x,))
                    return self.simplify() if simplify else self
                return self

            if new.has(x):
                diff = old - new
                if diff._has(x):
                    if old != x: 
                        return self
                    
                    expr = self.expr._subs(old, new)
                    if len(domain) == 2:
                        a, b = domain
                        if a.is_bool:
                            cond, baseset = domain
                            assert baseset.is_set
                            cond = cond._subs(old, new)                            
                            self = self.func(expr, (x, cond, baseset))
                        else:
                            from sympy import Element
                            cond = Element(new, x.range(a, b))
                            self = self.func(expr, (x, cond))
                    elif len(domain) == 1:
                        cond = domain[0]
                        if cond.is_bool:
                            cond = cond._subs(old, new)
                            self = self.func(expr, (x, cond))
                            
                    return self.simplify() if simplify else self
                    
                else: 
                    if old != x:
                        alpha = p.coeff_monomial(x)
                        diff /= alpha
                        
                    if diff.is_zero:
                        return self
                    
                    expr = self.expr._subs(x, x - diff)
                    if len(domain) == 2:
                        self = self.func(expr, (x, a + diff, b + diff))
                    elif len(domain) == 1:
                        cond = domain[0]
                        assert cond.is_bool
                        cond = cond._subs(x, x - diff)
                        self = self.func(expr, (x, cond))
                    else:
                        self = self.func(expr, (x,))
            else:
                if old != x:
                    sol = solve(old - new, x)
                    if len(sol) != 1:
                        return self
                    new = sol[0]
    
                _x = new.free_symbols - old.free_symbols
    
                if len(_x) != 1:
                    return self
                _x, *_ = _x
    
                expr = self.expr.subs(x, new)
    
                if domain:
                    a = solve(new - a, _x)
                    b = solve(new - b, _x)
                    if len(a) != 1 or len(b) != 1:
                        return self
                    a, b = a[0], b[0]
    
                    p = new.as_poly(_x)
                    alpha = p.coeff_monomial(_x)
                    if alpha > 0:
                        self = self.func(expr, (_x, a, b))
                    elif alpha < 0:
                        self = self.func(expr, (_x, b, a))
                    else:
                        return self
                else:
                    self = self.func(expr, (_x))
            return self.simplify() if simplify else self

        elif len(self.limits) == 0:
            expr = self.expr._subs(old, new)

            return self.func(expr, *self.limits)
        else: 
            
            if new in self.variables_set:
                d = Dummy(**new.type.dict)
                this = self.limits_subs(old, d)
                this = this.limits_subs(new, old)                
                return this.limits_subs(d, new)
            
            limits = [*self.limits]
            variables = self.variables
            hit = False
            for i, limit in enumerate(limits):
                x, *domain = limit
                if old == x and not new.has(x):
                    return self._subs_limits(x, domain, new, simplify=simplify)

                if len(domain) == 2:
                    a, b = domain

                p = old.as_poly(x)
                if p is None or p.degree() == 0:
                    continue
                if p.degree() != 1:
                    return self

                if new.has(x):
                    diff = old - new
                    if old != x:
                        if diff.has(x):
                            return self

                        alpha = p.coeff_monomial(x)
                        diff /= alpha

                    expr = self.expr.subs(x, x - diff)
                    
                    if diff.has(*variables[:i]):
                        return self
                    if domain:
                        limits[i] = (x, a + diff, b + diff)
                    for j in range(i):
                        var, *ab = limits[j]
                        if ab:
                            ab = [e._subs(x, x - diff) for e in ab]
                            limits[j] = (var, *ab)
                    hit = True
                break

            if not hit:
                return self.func(self.expr.subs(old, new), *self.limits)
            
            return self.func(expr, *limits)

        return self

    def _if_new_has_variables(self, old, new):
        return {x for x in new.free_symbols & self.variables_set - old.free_symbols if not old._has(x)}
    
    def _subs_if_new_has_variables(self, old, new, intersect=None): 
        this = self
        excludes = self.variables_set | new.free_symbols
        for var in intersect:
            _var = self.generate_var(excludes, **var.type.dict)
            this = this.limits_subs(var, _var)
            excludes.add(_var) 
        _this = this._subs(old, new)
        if _this == this:
            return self
        return _this
        
#     Override this stub if you want to do anything more than
#     attempt a replacement of old with new in the arguments of self.
    def _subs_utility(self, old, new, **hints):
        if old.is_Sliced:
            this = self._subs_sliced(old, new, **hints)
            if this != self:
                return this

        if old.is_symbol and not self.expr._has(old):
            if not any(limit._has(old) for limit in self.limits):
                return self
            
            intersect = self._if_new_has_variables(old, new)
            if intersect:
                return self._subs_if_new_has_variables(old, new, intersect)
            
            hit = False
            limits = [*self.limits]
            
            for i, limit in enumerate(self.limits):
                _limit = limit._subs_limits(old, new)
                if _limit != limit:
                    limits[i] = _limit
                    hit = True
            if hit:
                self = self.func(self.expr, *limits)
                if hints.get('simplify', True):
                    self = self.simplify()
            return self
            
        if not old.is_Surrogate:
            if intersect := self._if_new_has_variables(old, new):
                return self._subs_if_new_has_variables(old, new, intersect)
        
        from sympy.core.basic import _aresame
        if self == old or _aresame(self, old) or self.dummy_eq(old): 
            return new

        if old in self.variables_set:
            for i in range(len(self.limits) - 1, -1, -1):
                x = self.limits[i][0]
                if x != old:
                    continue
                
                hit = False
                limits = [*self.limits]
                
                limit = self.limits[i]
                
                if len(limit) <= 1 or not limit[1].is_bool:
                    _limit = limit._subs_limits(old, new)
                    if _limit != limit:
                        limits[i] = _limit
                        hit = True
                    
                for j in range(i + 1, len(self.limits)):
                    limit = self.limits[j]
                    _limit = limit._subs_limits(old, new)
                    if _limit != limit:
                        limits[j] = _limit
                        hit = True
                if hit:
                    self = self.func(self.expr, *limits)
                break
            return self
            
    def _subs_sliced_utility(self, old, new, **hints):
        if old.is_symbol and not self.expr._has(old):
            if not any(limit._has(old) for limit in self.limits):
                return self
            
            hit = False
            limits = [*self.limits]
             
            for i, limit in enumerate(self.limits):
                _limit = limit._subs_limits(old, new)
                if _limit != limit:
                    limits[i] = _limit
                    hit = True
            if hit:
                self = self.func(self.expr, *limits).simplify()
            return self
            
        intersect = {x for x in new.free_symbols & self.variables_set - old.free_symbols if not old._has(x)}            
        if intersect: 
            this = self
            excludes = self.variables_set | new.free_symbols
            for var in intersect:
                _var = self.generate_var(excludes, integer=True)
                this = this.limits_subs(var, _var)
                excludes.add(_var) 
            _this = this._subs_sliced(old, new)
            if _this == this:
                return self
            return _this
        
        from sympy.core.basic import _aresame
        if self == old or _aresame(self, old) or self.dummy_eq(old): 
            return new

        if old in self.variables_set:
            for i in range(len(self.limits) - 1, -1, -1):
                x = self.limits[i][0]
                if x != old:
                    continue
                
                hit = False
                limits = [*self.limits]
                
                limit = self.limits[i]
                
                if len(limit) and limit[1].is_bool:
                    ...
                else:
                    _limit = limit._subs_limits(old, new)
                    if _limit != limit:
                        limits[i] = _limit
                        hit = True
                    
                for j in range(i + 1, len(self.limits)):
                    limit = self.limits[j]
                    _limit = limit._subs_limits(old, new)
                    if _limit != limit:
                        limits[j] = _limit
                        hit = True
                if hit:
                    self = self.func(self.expr, *limits)
                break
            return self
        
        rule = OrderedDict()
        for limit in reversed(self.limits):
            x, *domain = limit
            if x.is_integer and len(domain) == 2:
                a, b = domain
                if a.free_symbols & rule.keys():
                    for args in rule.items():
                        a = a._subs(*args)
                if b.free_symbols & rule.keys():
                    for args in rule.items():
                        b = b._subs(*args)
                rule[x] = x.copy(domain=Range(a, b))
        expr = self.expr
        for args in rule.items():
            expr = expr._subs(*args)

        _function = expr._subs(old, new)
        if _function != expr:
            for args in reversed(rule.items()):
                _function = _function._subs(*reversed(args))

            return self.func(_function, *(limit._subs(old, new) for limit in self.limits))
            
    def _subs(self, old, new, **hints):
        this = self._subs_utility(old, new, **hints)
        if this is not None:
            return this
        
        if old.has(*self.variables) and not new.has(*self.variables):
            if new.free_symbols:
                return self
        
        from sympy.core.basic import _aresame
        expr, *limits = self.args
        expr = expr._subs(old, new)
        hit = not _aresame(expr, self.expr)
        
        for i, limit in enumerate(limits):
            x, *cond = limit
            try:
                x = x._subs(old, new)
            except Exception as e:
                if str(e) == 'empty slices':
                    return expr
                raise e
            
            innerHit = not _aresame(x, limit[0])
            for j, c in enumerate(cond):
                c = c._subs(old, new)
                if not _aresame(c, cond[j]):
                    innerHit = True
                    cond[j] = c
                
            if innerHit:
                limits[i] = (x, *cond)
                hit = True

        if hit:
            return self.func(expr, *limits)
        return self

    def _subs_sliced(self, old, new, **hints):
        this = self._subs_sliced_utility(old, new, **hints)
        if this is not None:
            return this
        
        if old.has(*self.variables) and not new.has(*self.variables):
            return self
        
        from sympy.core.basic import _aresame
        hit = False
        args = [*self.args]
        for i, arg in enumerate(args):
            if not hasattr(arg, '_eval_subs'):
                continue
            arg = arg._subs(old, new)    
            if not _aresame(arg, args[i]):
                hit = True
                args[i] = arg
        if hit:
            rv = self.func(*args)
            return rv
        return self
    
    def _has_symbol(self, pattern):
        if (hit := self._has_variable(pattern)) is not None:
            return hit
        
        return self.expr._has(pattern) or any(arg._has(pattern) for arg in self.limits)

    def _has_indexed(self, pattern):
        if (hit := self._has_variable(pattern)) is not None:
            return hit
        
        base = pattern.base
        if base.is_Indexed:
            base = base.base
            
        for path in self.finditer(base, definition=True):
            history = self.fetch_from_path(*path, history=True)
            
            if isinstance(path[-2], int):
                last = history[-2]
                length = 3
            else:
                last = history[-3]
                length = 4
                if len(history) >= length and history[-length].is_symbol:
                    last = history[-length]
                    length += 1

            if last.is_Indexed and len(history) >= length and history[-length].is_Sliced and history[-length].base == last:
                last = history[-length]

            if path[0]:
                if path[1]:
                    print("unresolved cases")
                    return True
                else:
                    if last._has(pattern):
                        return True
            else:
                history.insert(0, self)
                for this in reversed(history):
                    if this.is_ExprWithLimits:
                        last = last.expand_indices(this.limits)
                        if last._has(pattern):
                            return True
        else:
            return False
        
    def _has_sliced(self, pattern):
        if (hit := self._has_variable(pattern)) is not None:
            return hit
        
        base = pattern.base
        if base.is_Indexed:
            base = base.base
            
        for path in self.finditer(base, definition=True):
            if path[0]:
                print("unresolved cases")
                return True
            else:
                history = self.fetch_from_path(*path, history=True)
                last = history[-2]
                if last.is_Indexed and len(history) >= 3 and history[-3].is_Sliced and history[-3].base == last:
                    last = history[-3]
                
                last = last.expand_indices(self.limits)
                if last._has(pattern):
                    return last not in self.variables
        else:
            return False

    def _has_variable(self, pattern):
        for i, (x, *args) in enumerate(self.limits):
            if x == pattern:
                mapping = self.limits_dict
                domain = mapping.pop(x)
                if not isinstance(domain, list) and domain and domain.is_set and domain._has(pattern):
                    return True
                
                mapping = limits_dict(self.limits[i + 1:])
                    
                for k, domain in mapping.items():
                    if k._has(pattern) or not isinstance(domain, list) and domain and domain.is_set and domain._has(pattern):
                        return True
                    
                return False
        
    @cacheit
    def _has(self, pattern):
        """Helper for .has()"""
        if pattern.is_Symbol:
            return self._has_symbol(pattern)
        
        if pattern.is_Indexed:
            return self._has_indexed(pattern)
        
        if pattern.is_Sliced or pattern.is_SlicedIndexed:
            return self._has_sliced(pattern)
        
        return Expr._has(self, pattern)

    @classmethod
    def class_key(cls):
        """Nice order of classes. """
        return 6, 0, cls.__name__

    def _eval_shape(self):
        return self.expr.shape

    @cacheit
    def _eval_domain_defined(self, x, allow_empty=True, **_): 
        if x.dtype.is_set:
            return x.universalSet
        
        domain = x.domain
        if x in self.variables:
            return domain
                    
        for limit in self.limits:
            var, *ab = limit
            if var.is_Sliced:
                domain &= var._eval_domain_defined(x, allow_empty=allow_empty)
            else:
                domain &= var.domain_defined(x)
            for e in ab:
                domain &= e.domain_defined(x)
                
        if self.expr._has(x):
            bound_domain = self.expr.domain_defined(x)
            for limit in self.limits:
                bound_domain = bound_domain.adjust_domain(*limit)
                
            domain &= bound_domain
            if x not in self.expr.free_symbols:
                v = self.variable
                if not v.is_Sliced:
                    v_domain = self.limits_dict[v]
                    for var in self.expr.free_symbols:
                        if not var._has(v) or not var.is_Indexed:
                            continue
                        pattern = var.subs(v, Wild(v.name, **v.assumptions0))
                        res = x.match(pattern)
                        if res: 
                            t_, *_ = res.values()
                            if isinstance(v_domain, list) or t_ in v_domain:
                                expr = self.expr._subs(v, t_)
                                domain &= expr.domain_defined(x)
                                break
            
        return domain

    def match_index(self, expr):
        if len(self.limits) != 1:
            return
        
        i, *_ = self.limits[0]
        i_ = Wild(i.name)

        dic = expr.match(self.expr.subs(i, i_))
        if dic:
            return dic[i_]
    # this simplication procedure is not meant for Sum / Integral / Product, since redundant bound variable can influence the result
    def simplify(self, deep=False, **kwargs):
        limits = self.limits
        limits_dict = {}
        variables = []
        for var, *ab in limits:
            variables.append(var)
            limits_dict[var] = ab

        expr = self.expr
        varMapping = defaultdict(list)
        illegalVars = set()
        for i, (x, *ab) in enumerate(limits):
            effective_symbols = expr.effective_variable(x)
            if len(ab) >= 1 and ab[0].is_bool:
                for v in ab[0].yield_effective_variable(x):
                    self.merge_symbols(v, effective_symbols)
            for v in effective_symbols:
                if x != v:
                    if x.index_contains(v) or v.index_contains(x):
                        varMapping[x].append((v, *limits_dict[x]))
                    elif x._has(v):
                        illegalVars.add(v)
                        illegalVars.add(x)
                        for v, *_ in varMapping[x]:
                            illegalVars.add(v)
        if varMapping:
            hit = {}            
            limits = [*limits]
            for x, s in varMapping.items():
                if x in illegalVars:
                    continue

                if len(s) == 1:
                    s, = s
                    if s[0] in illegalVars:
                        continue

                    if s[0] in hit:
                        i = [v for v, *_ in limits].index(x)
                        del limits[i]
                        if s[1:]:
                            ab = hit[s[0]]
                            if ab:
                                assert len(s[1:]) == 1
                                assert s[1].is_bool
                                assert ab[0].is_bool
                                ab = (ab[0] & s[1],)
                            else:
                                ab = s[1:]
                                assert len(ab) == 1
                                assert ab[0].is_bool
                            hit[s[0]] = ab
                            i = [v for v, *_ in limits].index(s[0])
                            limits[i] = (s[0], *ab)
                                
                    else:
                        ab = s[1:]
                        if len(ab) > 1:
                            illegalVars.add(s[0])
                            continue
                        if len(ab) == 1:
                            cond, = ab
                            if cond.is_set:
                                illegalVars.add(s[0])
                                continue
                        i = [v for v, *_ in limits].index(x)
                        limits[i] = s
                        hit[s[0]] = ab
            if hit:
                return self.func(expr, *limits)
        return self

    @property
    def expr_within_context(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                expr = expr._subs(x, x.copy(domain=domain))
        return expr

    @property
    def limits_shape(self):
        from sympy.functions.elementary.integers import Ceil
        shape = []
        for x, *ab in self.limits:
            if not ab:
                domain = self.expr.domain_defined(x)
                shape.append(domain.size)
            elif len(ab) == 2:
                a, b = ab
                shape.append(b - a)
            else:
                [domain] = ab
                start, stop, step = domain.args
                shape.append(Ceil((stop - start) / step))
        shape.reverse()
        return tuple(shape)


class AddWithLimits(ExprWithLimits):
    r"""Represents unevaluated oriented additions.
        Parent class for Integral and Sum.
    """

    def __new__(cls, expr, *symbols, **assumptions):
        pre = _common_new(cls, expr, *symbols, **assumptions)
        if type(pre) is tuple:
            expr, limits, orientation = pre
        else:
            return pre
        
        if not expr:
            return expr
        expr *= orientation # orientation not used in ExprWithLimits
            
        return Expr.__new__(cls, expr, *limits, **assumptions)

    def _eval_adjoint(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.expr.adjoint(), *self.limits)

    def _eval_conjugate(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.expr.conjugate(), *self.limits)

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            if all([x.is_real for x in flatten(self.limits)]):
                return self.func(self.expr.transpose(), *self.limits)

    def _eval_factor(self, **hints):
        if 1 == len(self.limits):
            summand = self.expr.factor(**hints)
            if summand.is_Mul:
                out = sift(summand.args, lambda w: not set(self.variables) & w.free_symbols)
                return Mul(*out[True]) * self.func(Mul(*out[False]), *self.limits)
        else:
            summand = self.func(self.expr, *self.limits[0:-1]).factor()
            if not summand.has(self.variables[-1]):
                return self.func(1, [self.limits[-1]]).doit() * summand
            elif isinstance(summand, Mul):
                return self.func(summand, self.limits[-1]).factor()
        return self

    def _eval_expand_basic(self, **hints):
        summand = self.expr.expand(**hints)
#         if summand.is_Add and summand.is_commutative:
        if summand.is_Add:
            args = []
            for arg in summand.args:
                if arg._coeff_isneg():
                    args.append(-self.func(-arg, *self.limits))
                else:
                    args.append(self.func(arg, *self.limits))
            return Add(*args)
#             return Add(*[self.func(i, *self.limits) for i in summand.args])
        elif summand.is_DenseMatrix:
            return Matrix._new(summand.rows, summand.cols, [self.func(i, *self.limits) for i in summand._args])
        elif summand != self.expr:
            if summand._coeff_isneg():
                return -self.func(-summand, *self.limits)
            return self.func(summand, *self.limits)
        
        return self

    def _subs(self, old, new, **hints):
        expr = self.expr.subs(old, new)
        limits = [*self.limits]
        hit = expr != self.expr
        for i, (x, *ab) in enumerate(limits):
            ab = [t._subs(old, new) for t in ab]
            if x.is_Sliced:
                try:
                    x = x._subs(old, new)
                except Exception as e:
                    if e.args[0] == 'empty slices':
                        return expr
                    raise e

            elif x.is_Indexed or x.is_SlicedIndexed:
                x = x._subs(old, new)

            limits[i] = (x, *ab)
            hit |= limits[i] != self.limits[i]
            
        if hit:
            return self.func(expr, *limits)
        
        return self

    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices):
        return self.func(self.expr[indices], *self.limits)

        
class MINMAXBase(ExprWithLimits):
    
    def _eval_is_hyper_real(self):
        return self.expr.is_hyper_real
        
    def _eval_is_extended_real(self):
        for x, *ab in self.limits:
            
            if len(ab) == 2:
                a, b = ab
                if b.is_set:
                    return
                
                if self.expr.is_continuous_at(x, a, b):
                    continue
                return
            
            if len(ab) == 1:
                [domain] = ab
                if domain.is_Interval:
                    if domain.left_open or domain.right_open:
                        if self.expr.is_continuous_at(x, domain): 
                            return False
                return
            return

        return True

    def _eval_shape(self):
        return self.expr.shape
    
    def _eval_is_finite(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_finite
    
    def simplify(self, deep=False, **kwargs):
        if len(self.limits) == 1:
            limit, = self.limits
            if len(limit) == 2:
                x, domain = limit
                if domain.is_FiniteSet and len(domain) == 1:
                    return self.finite_aggregate(x, domain)			
            if self.expr.is_Piecewise:
                x, domain = limit.coerce_setlimit()
                return self.expr.as_multiple_terms(x, domain, self.func)

        (x, *ab), *limits = self.limits
        independent, dependent = self.expr.as_independent(x, as_Add=True)
        if not independent.is_zero: 
            if limits:
                expr = self.func(dependent, (x, *ab)) + independent
                return self.func(expr, *limits)
            else:
                return self.func(dependent, *self.limits) + independent
        
        independent, dependent = self.expr.as_independent(x, as_Add=False)
        if independent != S.One: 
            if independent.is_extended_negative:
                return self.reversed_type(dependent, *self.limits) * independent
            if independent.is_extended_positive:
                return self.func(dependent, *self.limits) * independent
            if independent._coeff_isneg():
                return -self.func.reversed_type(-self.expr, *self.limits)
            
        if self.expr.is_Log:
            return self.expr.func(self.func(self.expr.arg, *self.limits))
        
        return ExprWithLimits.simplify(self, deep=deep)
    
    def bounds(self, x, domain, cls):
        try:
            assert self.expr.infinitesimality is None
            from sympy import limit
            maxi = domain.max()
            if maxi.is_infinite:
                maxi = limit(self.expr, x, maxi)
            else:
                maxi = self.expr._subs(x, maxi, symbol=False)
        
            mini = domain.min()
            if mini.is_infinite:
                mini = limit(self.expr, x, mini)    
            else: 
                mini = self.expr._subs(x, mini, symbol=False)
            return cls(maxi, mini)
        except:
            return self
    
    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '%s[%s](%s)' % (self.__class__.__name__, limits, p._print(self.expr))
        return '%s(%s)' % (self.__class__.__name__, p._print(self.expr))
    
    def _lean(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '%s[%s](%s)' % (self.__class__.__name__, limits, p._print(self.expr))
        return '%s(%s)' % (self.__class__.__name__, p._print(self.expr))
    
    def _latex(self, p):
        name = self.__class__.__name__.lower()[:3]

        if len(self.limits) == 1: 
            tex = r"\%s\limits_{%s} " % (name, self.limits[0]._format_ineq(p))
        elif len(self.limits) == 0:
            tex = r"\%s " % name
        else:
            if all(len(limit) == 1 for limit in self.limits):
                tex = r"\%s\limits_{{%s}} " % (name, str.join(', ', [l._format_ineq(p) for l in self.limits]))
            else:
                tex = r"\%s\limits_{\substack{%s}} " % (name, str.join('\\\\', [l._format_ineq(p) for l in self.limits]))

        if isinstance(self.expr, Add):
            tex += r"\left(%s\right)" % p._print(self.expr)
        else:
            tex += p._print(self.expr)

        return tex

    @property
    def dtype(self):
        if not self.limits:
            if self.expr.is_set:
                return self.expr.etype
        return self.expr.dtype

    def doit(self, **hints):
        if len(self.limits) > 1:
            return self
        
        x, *domain = self.limits[0]
        if x.is_set:
            return self

        if not domain:
            domain = x.domain
            if domain.is_CartesianSpace:
                return self
            
            if domain.is_ComplexRegion:
                return self
        
        return self


class Minima(MINMAXBase):
    r"""Represents unevaluated MIN operator.
    Minima[f,x]
    minimizes f with respect to x.
    """
    
    __slots__ = ['is_commutative']
    operator = Min

    def __new__(cls, expr, *symbols, **assumptions):
        expr = sympify(expr) 
        return ExprWithLimits.__new__(cls, expr, *symbols, **assumptions)

    def _eval_is_zero(self):
        if self.expr.is_zero:
            return True

    def doit(self, **hints):
        x, *domain = self.limits[0]
        if len(self.limits) != 1 or x.is_set:
            return self
        
        if len(domain) == 1:
            [domain] = domain
        elif len(domain) == 2: 
            if domain[-1].is_set: 
                return self
            else:
                domain = x.range(*domain)
        else:
            domain = x.domain
                         
        if domain.is_CartesianSpace or not domain.etype.is_extended_real:
            return self

        if self.expr.infinitesimality is not None:
            expr, epsilon = self.expr.clear_infinitesimal()
            return self.func(expr, *self.limits).doit(**hints) + epsilon
        
        if hints.get('approximate'):
            expr, monotonicity = self.expr.monotonicity(x)
            if monotonicity > 0:
                return expr._subs(x, domain.min())
            elif monotonicity < 0:
                return expr._subs(x, domain.max())
            elif isinstance(expr, tuple):
                lower, upper = expr
                return lower
                
        return self
    
    def _eval_summation(self, f, x):
        return None
        
    def _eval_is_extended_negative(self):
        if not self.limits and self.expr.is_set:
            if self.expr.infimum().is_extended_negative:
                return True

    def _eval_is_extended_positive(self):
        if not self.limits and self.expr.is_set:
            if self.expr.infimum().is_extended_positive:
                return True
            
    # infimum returns the value which is bound to be below (<=) the minimum!
    def infimum(self):
        if not self.limits and self.expr.is_set:
            return self.expr.infimum()
        return self
    
    @classmethod
    def identity(cls, self, **_):
        return S.Infinity
    
    @classmethod
    def is_identity(cls, self):        
        return self.is_Infinity
    

MIN = Minima

                
class Maxima(MINMAXBase):
    r"""Represents unevaluated MAX operator.
    Maxima[f,x]
    maximizes f with respect to x.
    """
    
    __slots__ = ['is_commutative']
    operator = Max

    def __new__(cls, expr, *symbols, **assumptions):
        expr = sympify(expr)
        return ExprWithLimits.__new__(cls, expr, *symbols, **assumptions)

    def _eval_is_zero(self):
        if self.expr.is_zero:
            return True

    def doit(self, **hints):
        x, *domain = self.limits[0]
        if len(self.limits) != 1 or x.is_set:
            return self
            
        if len(domain) == 1:
            domain, = domain
        elif len(domain) == 2:
            if domain[-1].is_set: 
                return self
            else:
                domain = x.range(*domain)
        else:
            domain = x.domain
            
        if domain.is_CartesianSpace or not domain.etype.is_extended_real:
            return self

        if self.expr.infinitesimality is not None:
            expr, epsilon = self.expr.clear_infinitesimal()
            return self.func(expr, *self.limits).doit(**hints) + epsilon
        
        if hints.get('approximate'):
            expr, monotonicity = self.expr.monotonicity(x)
            if monotonicity > 0:
                return expr._subs(x, domain.max())
            elif monotonicity < 0:
                return expr._subs(x, domain.min())
            elif isinstance(expr, tuple):
                lower, upper = expr
                return upper

        return self
    
    def separate(self):
        (x, *_), *_ = self.limits
        if x.is_Sliced:
            z, x = x.pop()
            return self.func(self.func(self.expr, (x,)).simplify(), (z,))
        return self

    # supremum returns the value which is bound to be above (>=) the minimum!
    def supremum(self):
        if not self.limits and self.expr.is_set:
            return self.expr.supremum()
        return self

    def _eval_is_extended_positive(self):
        if not self.limits and self.expr.is_set:
            if self.expr.supremum().is_extended_positive:
                return True

    def _eval_is_extended_negative(self):
        if not self.limits and self.expr.is_set:
            if self.expr.supremum().is_extended_negative:
                return True

    @classmethod
    def identity(cls, self, **_):
        return S.NegativeInfinity
    
    @classmethod
    def is_identity(cls, self):        
        return self.is_NegativeInfinity


Maxima.reversed_type = MIN
MIN.reversed_type = Maxima


class ArgMinMaxBase(ExprWithLimits):

    def _eval_is_finite(self):
        expr, limit = self.args
        x, domain = limit.coerce_setlimit(expr)
        if domain.is_Range or domain.is_Interval:
            if domain.stop.is_finite and domain.start.is_finite:
                return True

    def _eval_is_extended_integer(self):
        return self.variable.is_extended_integer

    def _eval_is_extended_real(self):
        return self.variable.is_extended_real

    def _eval_is_rational(self):
        return self.variable.is_rational
        
    def _eval_is_extended_complex(self):
        return self.variable.is_extended_complex
        
    def _eval_is_zero(self):
        ...

    def _eval_is_extended_positive(self):
        expr, limit = self.args
        x, domain = limit.coerce_setlimit(expr)
        is_extended_positive = domain.is_extended_positive
        if is_extended_positive:
            return True
        if is_extended_positive == False:
            return False

    def _eval_is_extended_negative(self):
        expr, limit = self.args
        x, domain = limit.coerce_setlimit(expr)
        is_extended_negative = domain.is_extended_negative
        if is_extended_negative:
            return True
        if is_extended_negative == False:
            return False

    @cacheit
    def _eval_shape(self):
        shape = None
        for x, *_ in self.limits:
            x_shape = x.shape
            if shape is None:
                shape = x_shape
                continue
            if x_shape == shape:
                shape = (2, *shape)                
                continue
            assert x_shape == shape[1:], 'illegal shape %s' % x_shape
            shape = (shape[0] + 1, *x_shape)
                
        return shape
    
    def simplify(self, deep=False, **kwargs):
        if not self.limits:
            if self.expr.is_Stack:
                if len(self.expr.limits) == 1 and not self.expr.variable.shape:
                    expr = self.expr.expr
                    return self.func(expr, *self.expr.limits).simplify(**kwargs)
            return self
        * _, (x, *_) = self.limits
        independent, dependent = self.expr.as_independent(x, as_Add=True)
        if not independent.is_zero: 
            return self.func(dependent, *self.limits)
        
        independent, dependent = self.expr.as_independent(x, as_Add=False)
        if independent != S.One:
            if independent.is_extended_positive: 
                return self.func(dependent, *self.limits)
            if independent.is_extended_negative: 
                return self.reversed_type(dependent, *self.limits)            

        if self.expr._coeff_isneg():
            return self.func.reversed_type(-self.expr, *self.limits)
        if self.expr.is_Log:
            return self.func(self.expr.arg, *self.limits)
        
        return ExprWithLimits.simplify(self, deep=deep)
    
    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '%s[%s](%s)' % (self.__class__.__name__, limits, p._print(self.expr))
        return '%s(%s)' % (self.__class__.__name__, p._print(self.expr))
    
    def _lean(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '%s[%s](%s)' % (self.__class__.__name__, limits, p._print(self.expr))
        return '%s(%s)' % (self.__class__.__name__, p._print(self.expr))
    
    def _latex(self, p):
        name = self.__class__.__name__.lower()[3:6]
        name = r'\mathop{{\rm %s}^{-1}}' % name
        if len(self.limits) == 1:
            tex = r"%s\limits_{\substack{%s}} " % (name, self.limits[0]._format_ineq(p))
        else:
            if all(len(limit) == 1 for limit in self.limits):
                tex = r"%s\limits_{{%s}} " % (name, str.join(', ', [l._format_ineq(p) for l in self.limits]))
            else:
                tex = r"%s\limits_{\substack{%s}} " % (name, str.join('\\\\', [l._format_ineq(p) for l in self.limits]))

        if isinstance(self.expr, Add):
            tex += r"\left(%s\right)" % p._print(self.expr)
        else:
            tex += p._print(self.expr)

        return tex

    @property
    def dtype(self):
        return self.variable.dtype
    
    @classmethod
    def is_identity(cls, self):
        ...

    
class ArgMin(ArgMinMaxBase):
    r"""Represents unevaluated argmin operator.
    Minima[f,x]
    minimizes f with respect to x.
    """

    def __new__(cls, expr, *symbols, **assumptions):
        expr = sympify(expr)
        return ExprWithLimits.__new__(cls, expr, *symbols, **assumptions)

    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *domain = self.limits[0]
        if x.is_set:
            return self

        if len(domain) == 1:
            [domain] = domain
        elif len(domain) == 2: 
            if domain[-1].is_set: 
                return self
            else:
                domain = x.range(*domain)
        else:
            domain = x.domain
            if domain.is_CartesianSpace:
                return self
        assert self.expr.infinitesimality is None
        p = self.expr.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                if a.is_extended_positive:
                    return domain.min()
                elif a.is_extended_negative:
                    return domain.max()
                
            elif p.degree() == 0:
                return self
            elif p.degree() <= 0:
                from sympy.matrices.expressions.matexpr import Zeros
                return Zeros(*self.shape)
        elif self.expr.is_MinMaxBase:
            print('warning, unreliable implementation')
            return self.expr.func(*(self.func(arg, *self.limits).doit() for arg in self.expr.args))

        return self
    
            
class ArgMax(ArgMinMaxBase):
    r"""Represents unevaluated argmax operator.
    Maxima[f,x]
    maximizes f with respect to x.
    """

    def __new__(cls, expr, *symbols, **assumptions):
        expr = sympify(expr)
        return ExprWithLimits.__new__(cls, expr, *symbols, **assumptions)

    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *domain = self.limits[0]

        if len(domain) == 1:
            [domain] = domain
        elif len(domain) == 2: 
            if domain[-1].is_set: 
                return self
            else:
                domain = x.range(*domain)
        else:
            domain = x.domain
            if domain.is_CartesianSpace:
                return self

        p = self.expr.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                if a.is_extended_positive:
                    return domain.max()
                elif a.is_extended_negative:
                    return domain.min()
            elif p.degree() == 0:
                return self
            elif p.degree() <= 0:
                from sympy.matrices.expressions.matexpr import Zeros
                return Zeros(*self.shape)
        elif self.expr.is_MinMaxBase:
            print('error, unreliable implementation')
            return self.expr.func(*(self.func(arg, *self.limits).doit() for arg in self.expr.args))
                
        return self
    

ArgMax.reversed_type = ArgMin
ArgMin.reversed_type = ArgMax


class INFSUPBase(ExprWithLimits):
    
    is_super_real = True
    
    def _eval_is_extended_real(self): 
        return self.expr.is_extended_real
        
    def _eval_shape(self):
        return self.expr.shape
    
    def _eval_is_finite(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if domain is None or isinstance(domain, list):
                return

            if domain.is_Interval:
                return

            if domain.is_Range:
                a, b = domain.args
                if a.is_infinite or b.is_infinite:
                    return
        return expr.is_finite
    
    def simplify(self, deep=False, **kwargs):
        if len(self.limits) == 1:
            limit = self.limits[0]
            if len(limit) == 2:
                x, domain = limit
                if domain.is_FiniteSet and len(domain) == 1:
                    return self.finite_aggregate(x, domain)
            if self.expr.is_Piecewise:
                x, domain = limit.coerce_setlimit()
                return self.expr.as_multiple_terms(x, domain, self.func)

        (x, *ab), *limits = self.limits
        independent, dependent = self.expr.as_independent(x, as_Add=True)
        if not independent.is_zero: 
            if limits:
                expr = self.func(dependent, (x, *ab)) + independent
                return self.func(expr, *limits)
            else:
                if dependent == 0:
                    conds = []
                    from sympy import Unequal
                    for x, *ab in self.limits:
                        if len(ab) == 2:
                            a, b = ab
                            if a.is_bool:
                                conds.append(Unequal(b, x.emptySet))
                                conds.append(a.invert())
                            else:
                                domain = x.range(a, b)
                                conds.append(Unequal(domain, x.emptySet))
                        else:
                            [domain] = ab
                            if domain.is_set:
                                conds.append(Unequal(domain, x.emptySet))
                            else:
                                conds.append(domain.invert())
                    
                    return Piecewise((independent, Or(*conds)), (self.defaultValue, True))
                return self.func(dependent, *self.limits) + independent
        
        independent, dependent = self.expr.as_independent(x, as_Add=False)
        if independent != S.One: 
            if independent.is_extended_negative:
                return self.reversed_type(dependent, *self.limits) * independent
            if independent.is_extended_positive:
                return self.func(dependent, *self.limits) * independent
            if independent._coeff_isneg():
                return -self.func.reversed_type(-self.expr, *self.limits)
            
        if self.expr.is_Log:
            return self.expr.func(self.func(self.expr.arg, *self.limits))
        
        return ExprWithLimits.simplify(self, deep=deep)
    
    def bounds(self, x, domain, cls):
        try:
            assert self.expr.infinitesimality is None
            from sympy import limit
            maxi = domain.max()
            if maxi.is_infinite:
                maxi = limit(self.expr, x, maxi)
            else:
                maxi = self.expr._subs(x, maxi, symbol=False)
        
            mini = domain.min()
            if mini.is_infinite:
                mini = limit(self.expr, x, mini)    
            else: 
                mini = self.expr._subs(x, mini, symbol=False)
            return cls(maxi, mini)
        except:
            return self
    
    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '%s[%s](%s)' % (self.__class__.__name__, limits, p._print(self.expr))
        return '%s(%s)' % (self.__class__.__name__, p._print(self.expr))
    
    def _lean(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '%s[%s](%s)' % (self.__class__.__name__, limits, p._print(self.expr))
        return '%s(%s)' % (self.__class__.__name__, p._print(self.expr))
    
    def _latex(self, p):
        name = self.__class__.__name__.lower()[:3]

        if len(self.limits) == 1: 
            tex = r"\%s\limits_{%s} " % (name, self.limits[0]._format_ineq(p))
        elif len(self.limits) == 0:
            tex = r"\%s " % name
        else:
            if all(len(limit) == 1 for limit in self.limits):
                tex = r"\%s\limits_{{%s}} " % (name, str.join(', ', [l._format_ineq(p) for l in self.limits]))
            else:
                tex = r"\%s\limits_{\substack{%s}} " % (name, str.join('\\\\', [l._format_ineq(p) for l in self.limits]))

        if isinstance(self.expr, Add):
            tex += r"\left(%s\right)" % p._print(self.expr)
        else:
            tex += p._print(self.expr)

        return tex

    @property
    def dtype(self):
        if not self.limits:
            if self.expr.is_set:
                return self.expr.etype
        return self.expr.dtype

    def doit(self, **hints):
        if len(self.limits) > 1:
            return self
        
        x, *domain = self.limits[0]
        if x.is_set:
            return self

        if not domain:
            domain = x.domain
            if domain.is_CartesianSpace:
                return self
            
            if domain.is_ComplexRegion:
                return self
        
        return self

    def domain_definition(self, **_):
        expr, *limits = self.args
        cond = expr.domain_definition()
        if cond:
            return cond

        import std
        if (_limits := std.deleteIndices(limits, lambda limit: not cond._has(limit[0]))) is not None:
            limits = _limits
            if not limits:
                return cond
        from sympy import All
        return All(cond, *limits) 


class Inf(INFSUPBase):
    r"""Represents unevaluated MIN operator.
    Inf[f,x]
    minimizes f with respect to x.
    """
    
    __slots__ = ['is_commutative']
    operator = Min
    
    def __new__(cls, expr, *symbols, **assumptions):
        expr = sympify(expr) 
        return ExprWithLimits.__new__(cls, expr, *symbols, **assumptions)

    def _eval_is_zero(self):
        if self.expr.is_zero:
            return True

    def doit(self, **hints):
        x, *domain = self.limits[0]        
        if len(self.limits) != 1 or x.is_set:
            return INFSUPBase.doit(self, **hints)
        
        if len(domain) == 1:
            [domain] = domain
        elif len(domain) == 2: 
            if domain[-1].is_set: 
                return self
            else:
                domain = x.range(*domain)
        else:
            domain = x.domain
                         
        if domain.is_CartesianSpace or domain.is_ComplexRegion:
            return INFSUPBase.doit(self, **hints)

        if self.expr.infinitesimality is not None:
            expr, epsilon = self.expr.clear_infinitesimal()
            return self.func(expr, *self.limits).doit() + epsilon
        
        p = self.expr.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                b = p.nth(0)
                if a.is_positive:
                    return a * domain.min() + b
                elif a.is_negative:
                    return a * domain.max() + b
            elif p.degree() == 0:
                return p.nth(0)
            elif p.degree() < 0:
                return self.expr
        elif self.expr.is_MinMaxBase:
            return self.expr.func(*(self.func(arg, *self.limits).doit() for arg in self.expr.args))
        return self
    
    def _eval_summation(self, f, x):
        return None
        
    def _eval_is_extended_negative(self):
        if not self.limits and self.expr.is_set:
            if self.expr.infimum().is_extended_negative:
                return True

    def _eval_is_extended_positive(self):
        if not self.limits and self.expr.is_set:
            if self.expr.infimum().is_extended_positive:
                return True
            
    # infimum returns the value which is bound to be below (<=) the minimum!
    def infimum(self):
        if not self.limits and self.expr.is_set:
            return self.expr.infimum()
        return self
    
    @property
    def defaultValue(self):
        return S.Infinity

    identity = Minima.identity
    is_identity = Minima.is_identity

                
class Sup(INFSUPBase):
    r"""Represents unevaluated MAX operator.
    Sup[f,x]
    maximizes f with respect to x.
    """
    
    __slots__ = ['is_commutative']
    operator = Max

    def __new__(cls, expr, *symbols, **assumptions):
        expr = sympify(expr)
        return ExprWithLimits.__new__(cls, expr, *symbols, **assumptions)

    def _eval_is_zero(self):
        if self.expr.is_zero:
            return True

    def doit(self, **hints):
        x, *domain = self.limits[0]        
        if len(self.limits) != 1 or x.is_set:
            return INFSUPBase.doit(self, **hints)
            
        if len(domain) == 1:
            [domain] = domain
        elif len(domain) == 2: 
            if domain[-1].is_set: 
                return self
            else:
                domain = x.range(*domain)
        else:
            domain = x.domain
            
        if domain.is_CartesianSpace or domain.is_ComplexRegion:
            return INFSUPBase.doit(self, **hints)

        if self.expr.infinitesimality is not None:
            expr, epsilon = self.expr.clear_infinitesimal()
            return self.func(expr, *self.limits).doit() + epsilon
        
        p = self.expr.as_poly(x)

        if p is not None:
            if p.degree() == 1: 
                a = p.coeff_monomial(x)       
                b = p.nth(0)         
                if a.is_extended_positive:
                    return a * domain.max() + b
                elif a.is_extended_negative:
                    return a * domain.min() + b
            elif p.degree() == 0:
                return p.nth(0)
            elif p.degree() < 0:
                return self.expr
        elif self.expr.is_MinMaxBase:
            return self.expr.func(*(self.func(arg, *self.limits).doit() for arg in self.expr.args))
        return self
    
    def separate(self):
        (x, *_), *_ = self.limits
        if x.is_Sliced:
            z, x = x.pop()
            return self.func(self.func(self.expr, (x,)).simplify(), (z,))
        return self

    # supremum returns the value which is bound to be above (>=) the minimum!
    def supremum(self):
        if not self.limits and self.expr.is_set:
            return self.expr.supremum()
        return self

    def _eval_is_extended_positive(self):
        if not self.limits and self.expr.is_set:
            if self.expr.supremum().is_extended_positive:
                return True

    def _eval_is_extended_negative(self):
        if not self.limits and self.expr.is_set:
            if self.expr.supremum().is_extended_negative:
                return True

    @property
    def defaultValue(self):
        return S.NegativeInfinity

    identity = Maxima.identity
    is_identity = Maxima.is_identity

Sup.reversed_type = Inf
Inf.reversed_type = Sup


class Stack(ExprWithLimits):
    r"""Represents unevaluated Stack operator.
    >>> n = Symbol(integer=True, positive=True)
    >>> A = Symbol(shape=(n, n), real=True)
    >>> B = Symbol(shape=(n, n), real=True)
    >>> Discrete.Dot.eq.Lamda.apply(A @ B)
    """
    
    operator = BlockMatrix
    
    def __new__(cls, expr, *symbols, **assumptions):
        [*symbols] = symbols
        expr = sympify(expr)
        for i, limit in enumerate(symbols):
            if isinstance(limit, tuple) and len(limit) > 1:
                x, *domain = limit
                if 'domain' in x._assumptions:
#                     local variable
                    if len(domain) == 2:
                        if x.domain == x.range(*domain):
                            symbols[i] = x,
                            continue
                    _x = Symbol(x.name, integer=True)
                    symbols[i] = _x, *domain

                    expr = expr._subs(x, _x)
                if len(domain) == 1:
                    domain, = domain
                    assert domain.is_Range
                    if domain.step == 1:
                        mini = domain.min()
                        symbols[i] = x, 0, domain.max() - mini + 1
                        if mini != S.Zero:
                            expr = expr._subs(x, x + mini)

        return ExprWithLimits.__new__(cls, expr, *symbols, **assumptions)

    def _eval_is_zero(self):
        if self.expr.is_zero:
            return True

    def doit(self, deep=False, **hints):
        limit = self.limits[-1]
        x, a, b = limit
        diff = b - a
        if not diff.is_Number:
            return self
        
        limits = self.limits[:-1]
        if limits:
            expr = self.func(self.expr, *limits).doit(**hints)
        else:
            expr = self.expr
                    
        if deep:
            expr = expr.doit(deep=deep)
            
        array = tuple(expr._subs(x, sympify(i)) for i in range(diff))
        return BlockMatrix(array, shape=self.shape)

    def as_coeff_mmul(self):
        return 1, self

    def squeeze(self):
        if not self.expr._has(self.variables[-1]):
            limits = self.limits[:-1]
            if limits:
                return self.func(self.expr, *limits).squeeze()
            return self.expr
        return self
    
    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a Stack object!
        """
        if rhs.is_Stack:
            if lhs.limits == rhs.limits:
                from sympy import All
                return All(self.func(lhs.expr, rhs.expr), *lhs.limits).simplify()        

    @staticmethod
    def simplify_Lamda(self, squeeze=False):
        return self.func(self.expr.expr, *self.limits + self.expr.limits).simplify(squeeze=squeeze)

    def simplify(self, deep=False, squeeze=False, **kwargs):
        if deep:
            limits_dict = self.limits_dict
            expr = self.expr
            reps = {}
            for x, domain in limits_dict.items():
                if domain.is_set and domain.is_integer:
                    _x = x.copy(domain=domain)
                    expr = expr._subs(x, _x)                  
                    if 'wrt' in kwargs:
                        expr = expr.simplify(deep=True, **kwargs)                        
                    else:
                        expr = expr.simplify(deep=True, wrt=_x, **kwargs)
                    
                    reps[_x] = x
            if reps:
                for _x, x in reps.items():
                    expr = expr._subs(_x, x)
                if expr != self.expr:
                    return self.func(expr, *self.limits).simplify(squeeze=squeeze)
            
        for i, limit in enumerate(self.limits):
            x, *ab = limit
            if ab and len(ab) == 2: 
                a, b = ab
                if a == b:
                    expr = self.expr._subs(x, a)                    
                    limits = [*self.limits]
                    del limits[i]
                    if limits:
                        return self.func(expr, *limits).simplify(squeeze=squeeze)
                    return expr
                if a.is_zero:
                    if b.is_infinite:
                        limits = [*self.limits]
                        limits[i] = (x,)
                        return self.func(self.expr, *limits).simplify(squeeze=squeeze)
                else: 
                    expr = self.expr._subs(x, x + a)
                    limits = [*self.limits]
                    limits[i] = (x, 0, b - a)
                    return self.func(expr, *limits).simplify(squeeze=squeeze)
        
        if len(self.limits) > 1:
            this = self.func(self.expr, self.limits[0])
            this_simplified = this.simplify()
            if this == this_simplified:
                if squeeze:
                    *limits, (i, *ab) = self.limits[1:]
                    this = self.func(this, *limits)
                    if not this._has(i):
                        return this.simplify(squeeze=True)
                return self
            return self.func(this_simplified, *self.limits[1:]).simplify(squeeze=squeeze)

        if squeeze and not self.expr.has(*self.variables):
            return self.expr
        
        return self.expr.func.simplify_Lamda(self, squeeze=squeeze)

    def __getitem__(self, indices, **_):
        if (indices := self.simplify_indices(indices)) is None:
            return self

        expr = self.expr
        if isinstance(indices, (tuple, list)):
            variables_set = self.variables_set
            reps = {}
            
            limits = []
            for limit, index in zip(self.limits[::-1], indices):
                if isinstance(index, Tuple):
                    start, stop, step = index.slice_args
                    x, a, b = limit
                    assert step == 1, "cases for %s is not implemented" % index
                    assert start >= 0
                    start += a
                    
                    stop += a
                    assert stop <= b
                    limits.append((x, start, stop))
                    continue
                
                x, *domain = limit
                index = sympify(index)
                variables_set.remove(x)
                if x == index:
                    if len(domain) == 1:
                        [domain] = domain
                        start, stop, step = domain.args
                        if step != 1:
                            expr = expr. _subs(x, start + index * step)
                    continue

                for v in variables_set:
                    if not index._has(v):
                        continue
                    _v = Dummy(domain=v.domain_assumed, **v.type.dict)
                    _index = index._subs(v, _v)
                    if _index == index:
# if the substitution fails, it means that index has v only in its domain, not in its definition or explicit expression, 
# like i = Symbol(domain = Interval(j, oo)), where i has j, but only in its domain, not in its definition
                        continue
                    index = _index
                    reps[_v] = v
                    assert not index._has(v)
                    
                expr = expr._subs(x, index)  # .simplify() will result in prolonged process
                if not index._has(x): 
                    if expr._has(x):
                        for var in postorder_traversal(expr):
                            if var._has(x):
                                break
                        expr = expr._subs(var, var.definition)
                        expr = expr._subs(x, index)
                        assert not expr._has(x)

            if len(indices) > len(self.limits):
                expr = expr[indices[len(self.limits):]]
            elif len(indices) < len(self.limits): 
                if expr.is_zero:
                    shape = self.shape[len(indices):]
                    from sympy.matrices.expressions.matexpr import Zeros
                    return Zeros(*shape)
                expr = self.func(expr, *self.limits[:-len(indices)])
                
            for k, v in reps.items():
                expr = expr._subs(k, v)
                    
            if limits:
                limits.reverse()
                return self.func(expr, *limits)
            
            return expr
        
        if isinstance(indices, Tuple):
            start, stop, step = indices.slice_args
            x, *domain = self.limits[-1]
            if len(domain) == 2:
                S[0], n = domain
                self_step = 1
            elif len(domain) == 1:
                [domain] = domain
                self_start, self_stop, self_step = domain.args
                from sympy import Ceil
                n = Ceil((self_stop - self_start) / self_step)
            else:
                n = S.Infinity
                self_step = 1

            assert not start < 0, "out of bound exception: negative starting index"
            if start != 0:
                expr = expr._subs(x, x + start)
                stop -= start

                assert not stop > n, "out of bound exception!"
                start = 0
            else:
                if stop >= n and step == 1:
                    return self
                
            limits = [*self.limits]
            
            if step == 1:
                if start != 0:
                    expr = expr._subs(x, start + x * self_step)                    
                    stop -= start
                    start = 0
                    
                limits[-1] = x, 0, stop
                
                if self_step != 1:
                    expr = expr._subs(x, start + x * self_step)
            else:
                limits[-1] = x, Range(start, stop, step)
            return self.func(expr, *limits)

        * limits, (x, *ab) = self.limits
        
        if len(ab) == 1:
            [domain] = ab
            start, stop, step = domain.args
            if step != 1 or start != 0:
                expr = expr._subs(x, start + x * step)
                
        elif len(ab) == 2:
            start, stop = ab
            if start != 0:
                expr = expr._subs(x, start + x)
        
        if x != indices:
            indices = sympify(indices)
            for i, (k, *ab) in enumerate(limits):
                if indices._has(k):
                    k_ = expr.generate_var(integer=True, excludes=self.variables_set)
                    expr = expr._subs(k, k_)
                    limits[i] = (k_, *ab)

            expr = expr._subs(x, indices)
            if not indices._has(x) and expr._has(x):
                for var in postorder_traversal(expr):
                    if var._has(x):
                        break
                expr = expr._subs(var, var.definition)
                expr = expr._subs(x, indices)
                assert not expr._has(x)
                
        if limits:
            return self.func(expr, *limits)
        return expr

    @property
    def dtype(self):
        return self.expr.dtype
            
    @cacheit
    def _eval_shape(self):
        return self.limits_shape + self.expr.shape

    @property
    def cols(self):
        return self.shape[-1]

    @property
    def rows(self):
        if len(self.shape) == 1:
            return 1
        return self.shape[-2]

    # @property
    # def is_Matrix(self):
    #     return len(self.shape) == 2

    @property
    def is_square(self):
        return self.rows == self.cols

    def inverse(self):
        from sympy.matrices.expressions.inverse import Inverse
        return Inverse(self)

    def _eval_determinant(self, **kwargs):
        from sympy.concrete.products import Product
        if not self.is_square:
            return
        if self.is_upper or self.is_lower:
            i, *domain = self.limits[0]
            if len(domain) == 2:
                a, b = domain
            else:
                if not domain:
                    domain = i.domain
                elif len(domain) == 1:
                    domain = domain[0]
                assert domain.is_Range
                a, b = domain.min(), domain.max() + 1

            prod = Product[i:a:b](self[i, i])
            if kwargs.get('deep'):
                prod = prod.doit(**kwargs)
            return prod

    @property
    def is_lower(self):
        """Check if matrix is a lower triangular matrix. True can be returned
        even if the matrix is not square.

        Examples
        ========

        >>> from sympy import Matrix
        >>> m = Matrix(2, 2, [1, 0, 0, 1])
        >>> m
        Matrix([
        [1, 0],
        [0, 1]])
        >>> m.is_lower
        True

        >>> m = Matrix(4, 3, [0, 0, 0, 2, 0, 0, 1, 4 , 0, 6, 6, 5])
        >>> m
        Matrix([
        [0, 0, 0],
        [2, 0, 0],
        [1, 4, 0],
        [6, 6, 5]])
        >>> m.is_lower
        True

        >>> from sympy.abc import x, y
        >>> m = Matrix(2, 2, [x**2 + y, y**2 + x, 0, x + y])
        >>> m
        Matrix([
        [x**2 + y, x + y**2],
        [       0,    x + y]])
        >>> m.is_lower
        False

        See Also
        ========

        is_upper
        is_diagonal
        is_lower_hessenberg
        """
        j = self.generate_var(domain=Range(self.cols))
        i = j.generate_var(domain=Range(j))
        if self[i, j].is_zero:
            return True

        i = self.generate_var(domain=Range(self.rows))
        j = i.generate_var(domain=Range(i + 1, self.cols))
        if self[i, j].is_zero:
            return True

    @property
    def is_upper(self):
        """Check if matrix is an upper triangular matrix. True can be returned
        even if the matrix is not square.

        Examples
        ========

        >>> from sympy import Matrix
        >>> m = Matrix(2, 2, [1, 0, 0, 1])
        >>> m
        Matrix([
        [1, 0],
        [0, 1]])
        >>> m.is_upper
        True

        >>> m = Matrix(4, 3, [5, 1, 9, 0, 4 , 6, 0, 0, 5, 0, 0, 0])
        >>> m
        Matrix([
        [5, 1, 9],
        [0, 4, 6],
        [0, 0, 5],
        [0, 0, 0]])
        >>> m.is_upper
        True

        >>> m = Matrix(2, 3, [4, 2, 5, 6, 1, 1])
        >>> m
        Matrix([
        [4, 2, 5],
        [6, 1, 1]])
        >>> m.is_upper
        False

        See Also
        ========

        is_lower
        is_diagonal
        is_upper_hessenberg
        """
        
        j = self.generate_var(domain=Range(self.cols))
        i = j.generate_var(domain=Range(j + 1, self.rows))
        if self[i, j].is_zero:
            return True
        
        i = self.generate_var(domain=Range(self.rows))
        j = i.generate_var(domain=Range(i))
        if self[i, j].is_zero:
            return True

    def _latex(self, p):
        args = []
        expr, *limits = self.args
        for limit in limits:
            if len(limit) == 1:
                k, = limit
                if len(limits) == 1 and expr == k:
                    return r'\left[*\mathbb{N}\right]'

                args.append(p._print(k))
            elif len(limit) == 2:
                var, domain = limit
                op = ":"
                if domain.step == 1:
                    if domain.start == 0:
                        parmas = [var, domain.stop]
                        op = "<"
                    else:
                        parmas = [var, domain.start, domain.stop]
                else:
                    if domain.start == 0:
                        parmas = [var, '', domain.stop, domain.step]
                    else:
                        parmas = [var, *domain.args]
                args.append(op.join((p._print(e) for e in parmas)))
            elif len(limit) == 3:
                if limit[1] == 0:
                    args.append(r"%s<%s" % (p._print(limit[0]), p._print(limit[2])))
                else:
                    args.append(r"%s:%s:%s" % (p._print(limit[0]), p._print(limit[1]), p._print(limit[2])))

        tex = r"[%s]" % ','.join(args)

        from sympy import MatMul
        if isinstance(expr, (Add, Mul, MatMul)):
            tex += r"\left(%s\right)" % p._print(expr)
        else:
            tex += p._print(expr)

        return tex

    def _sympystr(self, p):
        limits = ', '.join([limit._format_ineq(p) for limit in self.limits])
        return 'Stack[%s](%s)' % (limits, p._print(self.expr))

    def _lean(self, p):
        limits = [limit._format_ineq(p, lt=True) for limit in self.limits]
        operator = " ".join(reversed(["[%s]" % limit for limit in limits]))
        return f'{operator} {p._print(self.expr)}'
    
    def _eval_is_finite(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_finite

    def _eval_is_extended_integer(self):
        return self.expr.is_extended_integer
    
    def _eval_is_super_integer(self):
        return self.expr.is_super_integer
    
    def _eval_is_extended_rational(self):
        return self.expr.is_extended_rational
    
    def _eval_is_hyper_rational(self):
        return self.expr.is_hyper_rational
    
    def _eval_is_super_rational(self):
        return self.expr.is_super_rational
    
    def _eval_is_extended_real(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_extended_real

    def _eval_is_hyper_real(self):
        return self.expr.is_hyper_real
    
    def _eval_is_super_real(self):
        return self.expr.is_super_real

    def _eval_is_extended_complex(self):
        return self.expr.is_extended_complex

    def _eval_is_hyper_complex(self):
        return self.expr.is_hyper_complex
    
    def _eval_is_extended_positive(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_extended_positive

    def _eval_is_extended_negative(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_extended_negative
    
    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            if len(self.shape) < 2:
                return self
            expr = self.expr
            if len(expr.shape) >= 2:
                return self.func(expr.T, *self.limits)
            if len(expr.shape) == 1:
                if expr.is_SlicedIndexed:
                    limit = self.limits[0]
                    if len(self.limits) == 1 and len(limit) == 3:
                        var, z, size = limit
                        if z == 0:
                            slices, indices = expr.slices_indices()
                            if len(indices) == 1:
                                [index] = indices
                                if index == var:
                                    slices = [slice(*s) for s in slices]
                                    slices.append(slice(size))
                                    return expr.base[tuple(slices)]
                    
                return

        start, offset = axis
        stop = start + offset
        if offset > 0 and stop < len(self.limits) or offset < 0 and start < len(self.limits):
            [*limits] = reversed(self.limits)
            limits.insert(stop, limits.pop(start))
            return self.func(self.expr, *reversed(limits)).simplify()

    def generate_int_limit(self, index=-1, excludes=None, generator=None, var=None):
        if self.expr.shape:
            len_shape = len(self.expr.shape)
            if index < 0:
                index = len(self.shape) + index
            if index < len_shape:
                return self.expr.generate_int_limit(index, excludes=excludes | self.variables_set, generator=generator, var=var)
            index -= len_shape
        limit = self.limits[index]
        if excludes:
            x, *ab = limit
            if x in excludes:
                kwargs = x.type.dict
                if not ab:
                    ab = x.domain.min(), x.domain.max() + 1
                if var is not None and var not in excludes:
                    x = var
                else:
                    x = generator.generate_var(excludes, **kwargs)
                return (x, *ab)
        return limit
        
    def _eval_domain_defined(self, x, **_):
        return ExprWithLimits._eval_domain_defined(self, x, allow_empty=False)        

    def domain_definition(self, **_):
        eqs = []
        for x, *ab in self.limits:
            if ab:
                a, b = ab
                eqs.append(a <= b)
        return And(*eqs)

    def unsqueeze(self, axis, size):
        if axis < len(self.limits):
            limits = [*self._limits]
            indices = [*self._variables]
            
            i = self.generate_var(excludes=set(self._variables), integer=True)
            
            axis = len(limits) - axis
            indices.insert(axis, i)
            limits.insert(axis, (i, 0, size))
            
            return Stack(self[indices], *limits)
        else:
            limits = [*self._limits]
            indices = [*self._variables]
            
            i = self.generate_var(excludes=set(self._variables), integer=True)
            
            axis = len(limits) - axis
            indices.insert(axis, i)
            limits.insert(axis, (i, 0, size))
            
            return Stack(self[indices], *limits)
    
    @cacheit
    def of_embedding(self):
        try:
            expr = self.expr
            embedding, (indices, *vars) = expr.of(Indexed[Expr, Indexed])
            vars = tuple(reversed(vars))
            if vars == self.variables:
                return embedding, indices
        except:
            ...

        return None, None
        
    @cacheit
    def of_conv1d(self):
        from sympy.concrete.summations import Sum
        from sympy.core.containers import Tuple
        from sympy.core.symbol import Symbol
        from sympy.functions.elementary.integers import Floor
        
        try:
            expr, (i, S[0], N_seq_length), (k, S[0], N_batch_size) = self.args
            
            (bias, (inputs, (W, d_i))), (S[d_i], minus_i, (S[1], (dilation_plus_one, N_seq_length_minus_i))) = expr.of(Sum[Add[Expr @ Indexed], Tuple[Max, Add[Min]]])
            minus_i, = set(minus_i) - {0}
            dilation = dilation_plus_one - 1
            if dilation == 1:
                S[i] = minus_i.of(1 - Symbol)
                padding = 1
                S[N_seq_length], S[i] = N_seq_length_minus_i.of(Symbol - Symbol) 
            elif N_seq_length_minus_i.is_Floor:
                N_seq_length_with_padding, S[i / dilation] = N_seq_length_minus_i.arg.of(Expr - Expr)
                padding, S[N_seq_length / dilation] = N_seq_length_with_padding.of(Add)
                padding = padding * dilation + 1
                S[padding / dilation], S[i / dilation] = minus_i.of(Expr - Floor)
            else:
                (S[i], scale), padding = minus_i.of(-Floor[Expr / Expr - Expr])
                if scale == dilation:
                    S[N_seq_length / dilation], S[i / dilation] = N_seq_length_minus_i.of(1 + Floor[Expr - Expr])
                else:
                    dilation /= scale
                    S[N_seq_length / dilation], S[i / dilation] = N_seq_length_minus_i.of(scale + Floor[Expr - Expr])
                    
                padding *= dilation
            
            if inputs.is_Add:
                args = inputs.args
                inputs = []
                for arg in args:
                    input, S[k], S[d_i * dilation + i - padding] = arg.of(Indexed)
                    inputs.append(input)
                    
                inputs = Add(*inputs)
            else:
                inputs, S[k], S[d_i * dilation + i - padding] = inputs.of(Indexed)
                
            stride = 1
            padding = (padding,)
            stride = (stride,)
            dilation = (dilation,)
            return inputs, W, bias, stride, padding, dilation
        except:
            return None, None, None, None, None, None
    
    @cacheit
    def of_unsqueeze(self, excludes=None):
        try:
            from sympy.core.singleton import S
            expr, *limits = self.args
            vars = self.variables
            if expr.is_Indexed:
                tensor, indices = expr.args[0], expr.args[1:]
                
                indices_set = set(indices)
                assert len(limits) > len(indices)
                for axis, (v, *ab) in enumerate(limits):
                    if excludes and -axis - 1 - len(expr.shape) in excludes:
                        continue
                     
                    if v not in indices_set:
                        break
                
                if excludes:
                    _vars = []
                    for _axis, v in enumerate(vars):
                        if _axis == axis:
                            continue
                        
                        if -_axis - 1 - len(expr.shape) in excludes:
                            v, a, b = limits[axis]
                            tensor = tensor.unsqueeze(-_axis - 1 - len(expr.shape), b - a)
                        else:
                            _vars.append(v)
                               
                    vars = tuple(_vars)
                else:
                    vars = vars[:axis] + vars[axis + 1:]
                    
                vars = vars[::-1]
                assert vars == indices
                
                assert len(tensor.shape) + 1 == len(self.shape)
                axis = len(limits) - axis - 1
                S[0], size = ab
                
            elif expr.is_AssocOp:
                tensors = []
                axes = set()
                sizes = set()
                for arg in expr.args:
                    if arg.has(*vars):
                        tensor, axis, size = self.func(arg, *limits).of_unsqueeze(excludes=excludes)
                        tensors.append(tensor)
                        axes.add(axis)
                        sizes.add(size)
                    else:
                        tensors.append(arg)
    
                tensor = None
                if any(t.is_Stack for t in tensors) and all(t.is_elementwise and t.arg.is_Stack for t in tensors if not t.is_Stack):
                    
                    limits = set()
                    for t in tensors:
                        if t.is_Stack:
                            limits.add(t.limits)
                        else:
                            limits.add(t.arg.limits)
                        
                    if len(limits) == 1:
                        limits, = limits
                        
                        exprs = []
                        for t in tensors:
                            if t.is_Stack:
                                exprs.append(t.expr)
                            else:
                                exprs.append(t.func(t.arg.expr))
                        tensor = Stack(expr.func(*exprs), *limits)
                        
                if tensor is None:
                    tensor = expr.func(*tensors)
                    
                axis, = axes
                size, = sizes
    
            elif expr.is_Sliced:
                tensor, axis, size = self.func(expr.base, *limits).of_unsqueeze(excludes=excludes)
                tensor = tensor[tuple((*[slice(None)] * (len(tensor.shape) - len(expr.indices)), *expr.indices))]
    
            elif expr.is_Pow:
                base, exp = expr.args
                assert exp.is_Number
                
                tensor, axis, size = self.func(expr.base, *limits).of_unsqueeze(excludes=excludes)
                tensor = expr.func(tensor, exp)
                
            elif expr.func.is_elementwise:
                tensor, axis, size = self.func(expr.arg, *limits).of_unsqueeze(excludes=excludes)
                tensor = expr.func(tensor)
                
            elif expr.is_Reduced and len(expr.arg.shape) == 1:
                if excludes is None:
                    excludes = (-1,)
                else:
                    excludes = tuple(e - 1 for e in excludes)
                    excludes += (-1,)
                
                tensor, axis, size = self.func(expr.arg, *limits).of_unsqueeze(excludes=excludes)
                
                if tensor.is_Stack:
                    tensor = tensor.func(expr.func(tensor.expr), *tensor.limits)
                else:
                    tensor = expr.func(tensor)
                    
            else:
                raise
    
            return tensor, axis, size
        except:
            return None, None, None

    def limits_in_context(self, has_args=None, parent=None):
        if has_args:
            return [*self.limits]
        from sympy import oo
        limits = []
        for limit in self.limits:
            x, *ab = limit
            if not ab:
                domain = self.expr.domain_defined(x)                     
                domain &= Range(0, oo)
                limit = (x, domain)
            limits.append(limit)
        limits.reverse()
        
        return limits
    
    @classmethod
    def is_identity(cls, expr):
        ... 

    def _eval_conjugate(self):
        expr, *limits = self.args
        return self.func(~expr, *limits)


from sympy.concrete.limits import *
