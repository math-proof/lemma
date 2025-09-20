from sympy.logic.boolalg import Boolean
from sympy.concrete.expr_with_limits import ExprWithLimits
from sympy.core.sympify import sympify
from sympy.utilities.iterables import postorder_traversal


class Quantifier(Boolean, ExprWithLimits):
    """Quantifier is the base class for All and Any"""
    
    __slots__ = []

    _op_priority = 12.1  # higher than Relational

    def __getitem__(self, rhs):
        return self.func(self.expr[rhs], *self.limits)

    def __mul__(self, rhs):
        return self.func(self.expr * rhs, *self.limits)
        
    def __mod__(self, rhs):
        return self.func(self.expr % rhs, *self.limits)
    
    def __truediv__(self, rhs):
        return self.func(self.expr / rhs, *self.limits)

    def __matmul__(self, rhs):
        return self.func(self.expr @ rhs, *self.limits)
    
    def __rmatmul__(self, lhs):
        return self.func(lhs @ self.expr, *self.limits)
    
    @property
    def T(self):
        return self.func(self.expr.T, *self.limits)
    
    def inverse(self):
        return self.func(self.expr.inverse(), *self.limits)

    def funcs(self):
        funcs = [(self.func, self.limits)]
        function = self.expr
        if function.is_Quantifier:
            sub_funcs, function = function.funcs()
            funcs = sub_funcs + funcs

        return funcs, function

    def apply(self, axiom, *args, **kwargs):
        given = self
        
        if axiom.apply.__name__ == 'given':
            join = False
        elif 'join' in kwargs:
            join = kwargs['join']
            del kwargs['join']
        else:
            join = True

        if join and args and all(isinstance(eq, Boolean) for eq in args):
            args = [given, *args]
            given = And(*args, evaluate=False, equivalent=args)
            return given.apply(axiom, split=True, **kwargs)
        
        if 'depth' in kwargs:
            depth = kwargs['depth']
            if not depth: 
                del kwargs['depth']
                if 'split' in kwargs:
                    eqs = self.split()
                    self, *rest = eqs
                    args = tuple(rest) + args
                    del kwargs['split']
                return Boolean.apply(self, axiom, *args, **kwargs)
            else:
                kwargs['depth'] -= 1
        else:
            return Boolean.apply(self, axiom, *args, **kwargs)
        return self.this.expr.apply(axiom, *args, **kwargs)

    @property
    def reversed(self):
        return self.func(self.expr.reversed, *self.limits)

    def __neg__(self):
        return self.func(-self.expr, *self.limits)

    def limits_include(self, eq):
        variables = self.variables_set
        _variables = eq.variables_set
        for v in variables:
            if v in _variables:
                _variables.remove(v)
            elif v.is_Sliced:
                for _v in _variables:
                    if v.index_contains(_v):
                        _variables.remove(_v)
                        break

            else:
                continue
        return not _variables

    def __invert__(self):
        function = self.expr.invert()
        return self.invert_type(function, *self.limits, negation=self)

    def invert(self):
        function = self.expr.invert()
        return self.invert_type(function, *self.limits)

    def __and__(self, eq):
        """Overloading for & operator"""
        return Boolean.__and__(self, eq)

    def bfn(self, bfn, eq):
        if self.is_Exists:
            func = self.func
            if eq.is_Exists:
                if self.limits == eq.limits:
                    limits = self.limits
                else:
                    limits = self.limits + eq.limits

                result = getattr(self.expr, bfn)(eq.expr)
            else:
                limits = self.limits
                result = getattr(self.expr, bfn)(eq)
        else:
            if eq.is_Exists:
                if self.expr.is_Exists and self.expr.limits == eq.limits:
                    func = self.func
                    limits = self.limits
                    result = getattr(self.expr, bfn)(eq)
                else:
                    limits = eq.limits
                    func = eq.func

                    dic = eq.limits_common(self)
                    if dic:
                        _self = self.func(self.expr, *self.limits_delete(dic))

                        result = getattr(_self, bfn)(eq.expr)
                        result.given = True
                    else:
                        result = self.bfn(bfn, eq.expr)
            elif eq.is_ForAll:
                func = self.func
                if self.limits == eq.limits:
                    limits = self.limits
                else:
                    limits = self.limits + eq.limits
                result = getattr(self.expr, bfn)(eq.expr)
            else:
                func = self.func
                limits = self.limits
                result = getattr(self.expr, bfn)(eq)

        equivalent = [self, eq] if eq.is_Boolean else self
        kwargs = {}
        if result.equivalent is not None:
            kwargs['equivalent'] = equivalent
        elif result.given is not None:
            kwargs['given'] = equivalent

        return func(result, *limits, **kwargs).simplify()

    @property
    def etype(self):
        return self.expr.etype

    @property
    def lhs(self):
        return self.expr.lhs

    @property
    def rhs(self):
        return self.expr.rhs

    def __add__(self, eq):
        eq = sympify(eq)
        return self.bfn('__add__', eq)

    def __sub__(self, eq):
        eq = sympify(eq)
        return self.bfn('__sub__', eq)

    def __bool__(self):
        return False

    def simplify(self, deep=False, **kwargs):
        from sympy import S
        if self.expr.func == self.func:
            exists = self.expr
            return self.func(exists.expr, *exists.limits + self.limits).simplify()

        this = self.delete_independent_variables()
        if this is not None:
            return this
        
        function = self.expr
        if function.is_And or function.is_Or:
            for t in range(len(self.limits)):
                x, *domain = self.limits[t]
                index = []
                for i, eq in enumerate(function.args):
                    if eq._has(x):
                        index.append(i)
                if len(index) == 1:
                    
                    if any(limit._has(x) for limit in self.limits[:t]):
                        continue
                    
                    if len(domain) == 1 and domain[0].is_bool:
                        continue
                    
                    [index] = index
                    eqs = [*function.args]

                    eqs[index] = self.func(eqs[index], (x, *domain)).simplify()
                    limits = self.limits_delete(x)
                    
                    if limits:
                        function = function.func(*eqs)                        
                        return self.func(function, *limits).simplify()
                    else:
                        return function.func(*eqs)
            limits_cond = self.limits_cond
            for i, eq in enumerate(self.expr.args):
                eq &= limits_cond
                copy = False
                shrink = False
                if eq:
                    if self.expr.is_Or:
                        copy = True
                    else:
                        shrink = True
                elif eq.is_BooleanFalse:
                    if self.expr.is_And:
                        copy = True
                    else:
                        shrink = True

                if copy:
                    return eq
                if shrink:
                    args = [*self.expr.args]
                    del args[i]
                    function = self.expr.func(*args)
                    return self.func(function, *self.limits).simplify()

        if deep:
            function = self.expr
            reps = {}
            for x, domain in limits_dict.items():
                if domain.is_set and domain.is_integer:
                    _x = x.copy(domain=domain)
                    function = function._subs(x, _x).simplify(deep=deep)
                    reps[_x] = x
            if reps:
                for _x, x in reps.items():
                    function = function._subs(_x, x)
                if function != self.expr:
                    return self.func(function, *self.limits).simplify()

        for i, (x, *domain) in enumerate(self.limits):
            if len(domain) == 1:
                domain, = domain
                if domain.is_FiniteSet and len(domain) == 1:
                    new, = domain
                    [*limits] = self.limits
                    expr, limits = Quantifier.expr_subs(self.expr, limits, x, new, i)
                    expr = self.finite_aggregate(x, domain)
                    del limits[i]
                    return self.func(expr, *limits).simplify()
                if domain.is_Element:
                    if domain.lhs == x:
                        domain = domain.rhs
                        limits = self.limits_update({x:domain})
                        return self.func(self.expr, *limits).simplify()

                elif domain.is_ConditionSet:
                    if x == domain.variable: 
                        condition = domain.condition
                    else:
                        condition = domain.condition._subs(domain.variable, x)                        
                        
                    limits = [*self.limits]
                    if domain.base_set.is_UniversalSet:
                        limits[i] = (x, condition)
                    else:
                        limits[i] = (x, condition, domain.base_set)
                    return self.func(self.expr, *limits).simplify()

                elif domain.is_UniversalSet and x.dtype in domain.etype:
                    limits = [*self.limits]
                    limits[i] = (x,)
                    return self.func(self.expr, *limits).simplify()

        for i, limit in enumerate(self.limits):
            if len(limit) == 1:
                continue
            if len(limit) == 3:
                e, cond, baseset = limit
                if baseset.is_set:
                    if cond == self.expr: 
                        return S.BooleanTrue
            else:
                e, s = limit
                if s.is_set:
                    if s.is_Symbol or s.is_Indexed:
                        continue
                    
                    if s.is_Piecewise:
                        if s.args[-1][0].is_EmptySet:
                            s = s.func(*s.args[:-2], (s.args[-2][0], True))                            
                        
                            limits = [*self.limits]
                            limits[i] = (e, s)
                            return self.func(self.expr, *limits).simplify()
                        continue
                    
                    image_set = s.image_set()
                    if image_set is not None:
                        sym, expr, base_set = image_set
                        if self.expr.is_ExprWithLimits:
                            if sym in self.expr.bound_symbols:
                                _sym = base_set.element_symbol(self.expr.variables_set)
                                assert sym.shape == _sym.shape
                                _expr = expr.subs(sym, _sym)
                                if _expr == expr:
                                    for var in postorder_traversal(expr):
                                        if var._has(sym):
                                            break
                                    expr = expr._subs(var, var.definition)
                                    _expr = expr._subs(sym, _sym)
    
                                expr = _expr
                                sym = _sym
                            assert sym not in self.expr.bound_symbols
                        
                        function = self.expr
                        if e != expr:
                            if sym.type == e.type:
                                _expr = expr._subs(sym, e)
                                if _expr != e:
                                    _function = function._subs(e, expr)
                                    if _function == function:
                                        return self
                                    limits = self.limits_update({e: (sym, base_set)})
                                    for j in range(i):
                                        x, *ab = limits[j]
                                        limits[j] = x, *(c._subs(e, expr) for c in ab)

                                    function = _function
                                else:
                                    base_set = base_set._subs(sym, e)
                                    limits = self.limits_update(e, base_set)
                            else:
                                _function = function._subs(e, expr)
                                if _function == function:
                                    return self
                                limits = self.limits_update({e: (sym, base_set)})
                                function = _function
                        else:
                            limits = self.limits_update({e: (sym, base_set)})                            
                        return self.func(function, *limits).simplify(**kwargs)
                else:  # s.type.is_bool: 
                    if s.is_Equal:
                        if e == s.lhs:
                            y = s.rhs
                        elif e == s.rhs:
                            y = s.lhs
                        else:
                            y = None
                        if y is not None and not y.has(e):
                            function = function._subs(e, y)
                            if function.is_BooleanAtom:
                                return function
                            limits = self.limits_delete(e)
                            if limits:
                                return self.func(function, *limits)
                            return function
                    if s == self.expr or s.dummy_eq(self.expr):  # s.invert() | self.expr
                        return S.BooleanTrue

        return ExprWithLimits.simplify(self, deep=deep)

    def doit(self, **hints):
        function = self.expr.doit(**hints)
        limits = []
        for i in range(len(self.limits) - 1, -1, -1):
            limit = self.limits[i]            
            if limit.is_intlimit:
                x, a, b = limit
                diff = b - a
                if diff.is_Number:
                    limits_behind = limits[::-1]
                    functions = []
                    for j in range(diff):
                        limits_before = [self.limits[t]._subs(x, a + j) for t in range(i)]                        
                        limits = limits_before + limits_behind
                        
                        functions.append(self.func(function._subs(x, a + j), *limits).doit(**hints).simplify())

                    return self.operator(*functions)
            else:
                limit = limit.doit()
                x, *ab = limit
                if x.is_Matrix:
                    if ab:
                        if x.is_BlockMatrix:
                            flat_list = x.args
                        else:
                            flat_list = x._args
                            
                        for arg in flat_list[:0:-1]:
                            limits.append((arg,))
                        limits.append((flat_list[0], *ab))
                    else:
                        for arg in x._args[::-1]:
                            limits.append((arg,))
                    continue

            limits.append(limit)
        return self.func(function, *limits[::-1])

    def _pretty(self, p, func):
        from sympy.printing.pretty.stringpict import prettyForm, stringPict
        prettyFunc = p._print("%s[%s]" % (func,
                                          ','.join([limit._format_ineq(p) for limit in self.limits])))
        prettyArgs = prettyForm(*p._print_seq([self.expr], delimiter=', ').parens())
        
        pform = prettyForm(binding=prettyForm.FUNC, *stringPict.next(prettyFunc, prettyArgs))

        # store pform parts so it can be reassembled e.g. when powered
        pform.prettyFunc = prettyFunc
        pform.prettyArgs = prettyArgs

        return pform

    def existent_symbols(self):
        free_symbols = Boolean.existent_symbols(self)        
        bound_symbols = {var.base: var.indices for var in self.bound_symbols if var.is_Sliced}

        if bound_symbols:
            deletes = set()
            for symbol in free_symbols: 
                if symbol.is_Indexed:
                    base = symbol.base
                    if base in bound_symbols:
                        slices = bound_symbols[base]
                        if len(symbol.indices) == len(slices) and \
                        all(k >= b and b < e for k, (b, e) in zip(symbol.indices, slices)):
                            deletes.add(symbol)

            free_symbols -= deletes
            
        return free_symbols

    def detect_previous_dependence(self, i, x):
        for j in range(i - 1, -1, -1):
            limit = self.limits[j]
            t, *ab = limit
            if t == x:
                if len(ab) == 2:
                    a, b = ab
                    if b._has(x) or not b.is_set and a._has(x):
                        return True
                                                                
                elif len(ab) == 1:
                    [cond] = ab
                    if not cond.is_bool and cond._has(x):
                        return True
                break
            
            if limit._has(x):
                return True
        
    def subs_with_independent_variable(self, i, x, y):
        limits = [*self.limits]  
        for j in range(i - 1, -1, -1):
            t, *ab = self.limits[j]
            if t == x:
                if len(ab) == 2:
                    a, b = ab
                    b = b._subs(x, y)
                    if not b.is_set:
                        a = a._subs(x, y)
                    # else:
                        # t is controled by conditionset or imageset!
                    limits[j] = (t, a, b)                                        
                elif len(ab) == 1:
                    [cond] = ab
                    if not cond.is_bool:
                        cond = cond._subs(x, y)
                        limits[j] = (t, cond)

                break
            t = t._subs(x, y)
            limits[j] = (t, *(c._subs(x, y) for c in ab))
            
        del limits[i]
        return self.func(self.expr, *limits).simplify()

    def delete_independent_variables(self):
        limits_dict = self.limits_dict
        function = self.expr
        for i, x in enumerate(self.variables):
            if function._has(x) or any(limit._has(x) for limit in self.limits[:i]):
                continue
            
            cond = limits_dict[x]
            if isinstance(cond, list) and cond:
                cond, baseset = cond
                if self.detect_previous_dependence(i, x):
                    continue
                
                limits = [*self.limits]
                del limits[i]
                if cond.is_bool:
                    # conditionset
                    cond = self.reduced_cond(x, cond, baseset)
                else:
                    # imageset
                    cond = self.reduced_cond(x, baseset)
                    
                if limits:
                    expr = self.func(self.expr, *limits).simplify()
                else:
                    expr = self.expr
                return self.invert_type.operator(cond, expr)

            if cond is None:
                if self.detect_previous_dependence(i, x):
                    continue
                
                limits = [*self.limits]
                del limits[i]
                if limits:
                    return self.func(self.expr, *limits).simplify()
                else:
                    return self.expr.simplify()
                    
            if cond.is_bool:
                if cond.is_Equal and x in cond.args:
                    y = cond.rhs if x == cond.lhs else cond.lhs
                    return self.subs_with_independent_variable(i, x, y)
                if cond.is_Element and cond.lhs == x and cond.rhs.is_FiniteSet and len(cond.rhs) == 1:
                    y, = cond.rhs.args
                    return self.subs_with_independent_variable(i, x, y)
                
                if self.detect_previous_dependence(i, x):
                    continue
                
                limits = [*self.limits]
                del limits[i]          
                cond = self.reduced_cond(x, cond)
                if limits:
                    expr = self.func(self.expr, *limits).simplify()
                else:
                    expr = self.expr
                return self.invert_type.operator(cond, expr)
            
            if cond.is_FiniteSet and len(cond) == 1: 
                y, = cond.args
                return self.subs_with_independent_variable(i, x, y)
            
            if self.detect_previous_dependence(i, x):
                continue
            
            limits = [*self.limits]
            del limits[i]
            cond = self.reduced_cond(x, cond)
            if limits:
                expr = self.func(self.expr, *limits).simplify()
            else:
                expr = self.expr
            return self.invert_type.operator(cond, expr)

    def _latex(self, p):
        latex = p._print(self.expr)
        if self.expr.is_LatticeOp:
            latex = r"\left(%s\right)" % latex

        if all(len(limit) == 1 for limit in self.limits):
            limit = '\\ '.join(var.latex for var, *_ in self.limits)
        else:
            limits = []
            for limit in self.limits:
                var, *args = limit
                if len(args) == 0:
                    limit = var.latex
                elif len(args) == 1:
                    limit = var.domain_latex(args[0])
                else:
                    a, b = args
                    if b.is_set:
                        limit = var.domain_latex(a, baseset=b)
                    else:
                        limit = var.domain_latex(var.range(*args))

                limits.append(limit)

            limit = r'\substack{%s}' % '\\\\'.join(limits)

        latex = r"\%s_{%s}{%s}" % (self.latexname, limit, latex)
        return latex

    @property
    def canonical(self):
        return self
    
from sympy.concrete.limits import *
