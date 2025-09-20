from sympy.concrete.expr_with_limits import ExprWithLimits, Minima, Maxima
from sympy.sets.sets import Set, Union, FiniteSet, Interval, Intersection,\
    conditionset
from sympy.core.symbol import Symbol, Wild
from sympy.tensor.indexed import Indexed, Sliced
from sympy.core.sympify import sympify
from sympy.functions.elementary.piecewise import Piecewise
from sympy.logic.boolalg import And
from sympy.sets.fancysets import Range
from sympy.logic.boolalg import Or
from sympy.core.singleton import S
from sympy.utilities.iterables import sift
from itertools import zip_longest


class Cup(Set, ExprWithLimits):
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
    
    operator = Union

    @property
    def is_ConditionSet(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        x, *_ = limit
        if not isinstance(x, (Symbol, Indexed, Sliced)):
            return False
        if not isinstance(self.expr, FiniteSet) or len(self.expr) != 1:
            return False
        element, *_ = self.expr
        if element != x:
            return False
        if len(limit) <= 1:
            return False
        if len(limit) == 2:
            return True
        
        return limit[2].is_set

    def handle_finite_sets(self, unk):
        if self.is_ConditionSet:
            return conditionset(self.variable, self.condition, self.base_set & unk)            
        else:
            match_index = self.match_index(unk)
            if match_index is not None:
                if match_index in self.limits_dict[self.variable]:
                    return unk
            
    def intersection_sets(self, b):
        if self.is_ConditionSet:
            if b.is_ConditionSet and self.variable == b.variable:
                return conditionset(self.variable, self.condition & b.condition, self.base_set & b.base_set)
            base_set = self.variable.domain & self.base_set
            if base_set in b:
                return self
            return conditionset(self.variable, self.condition, self.base_set & b)
    
    @property
    def condition(self):
        if self.is_ConditionSet:
            return self.limits[0][1]
        
    def condition_set(self):
        if self.is_ConditionSet:
            return self
        
    @property
    def base_set(self):
        if self.is_ConditionSet:
            limit = self.limits[0]
            if len(limit) > 2:
                return limit[2]
            return limit[0].universalSet

    def doit(self, **hints):
        *limits, limit = self.limits
        i, a, b = limit
        dif = b - a
        if not dif.is_Integer:
            return self
        
        if limits:
            expr = self.func(self.expr, *limits)
        else:
            expr = self.expr
        
        return Union(*[expr._subs(i, index + a) for index in range(dif)])

    def swap(self):
        if not self.expr.is_Cup:
            return self
        U = self.expr

        return U.func(self.func(U.expr, *self.limits).simplify(), *U.limits)

    # this will change the default new operator!
    def __new__(cls, expr, *symbols, **assumptions):
        expr = sympify(expr)
        if expr.is_EmptySet or expr.is_UniversalSet:
            return expr
        return ExprWithLimits.__new__(cls, expr, *symbols, **assumptions)

    def simplify(self, deep=False, **kwargs):
        if deep:
            _self = ExprWithLimits.simplify(self, deep=True)
            if _self != self:
                return _self

        if self.expr.is_Intersection:
            independent = set()
            for arg in self.expr.args:
                if not arg.has(*self.variables):
                    independent.add(arg)
            if independent:
                dependent = self.expr._argset - independent
                expr = self.expr.func(*dependent)
                independent = self.expr.func(*independent)
                return self.func(expr, *self.limits) & independent

        if self.expr.is_EmptySet:
            return self.expr
        
        if len(self.limits) == 1:
            limit, = self.limits

            if len(limit) == 2:
                from sympy.core.relational import Unequal
                x, domain = limit

                if not self.expr._has(x):
                    if domain.is_bool:
                        domain = conditionset(x, domain).simplify()
                    return Piecewise((self.expr, Unequal(domain, x.emptySet).simplify()), (self.expr.etype.emptySet, True)).simplify()
                
                if domain.is_FiniteSet and len(domain) == 1:
                    return self.finite_aggregate(x, domain)

                if domain.is_EmptySet:
                    return self.expr.etype.emptySet

                if domain.is_Union:
                    args = []
                    success = False
                    for dom in domain.args:
                        arg = self.func(self.expr, (x, dom)).simplify()
                        args.append(arg)
                        if not arg.is_Cup or arg.expr != self.expr:
                            success = True
                    if success:
                        return Union(*args)

                if domain.is_Range:
                    return self.func(self.expr, (x, domain.min(), domain.max() + 1))

                if self.expr.is_Complement:
                    A, B = self.expr.args
                    if not B.has(*self.variables):
                        return self.func(A, *self.limits) // B

                if domain.is_Piecewise:
                    tuples = []
                    for e, c in domain.args: 
                        tuples.append((self.func(self.expr, (x, e)).simplify(), c))    
                    return domain.func(*tuples)
                if domain.is_bool:
                    if domain.is_Equal:
                        if domain.lhs == x:
                            return self.expr._subs(x, domain.rhs)
                        elif domain.rhs == x:
                            return self.expr._subs(x, domain.lhs)
                    elif domain.is_Element:
                        if domain.lhs == x:
                            return self.func(self.expr, (x, domain.rhs))
                    
                if domain.is_set:
                    if not domain.is_symbol:
                        image_set = domain.image_set()
                        if image_set:
                            expr, sym, base_set = image_set
                            expr = self.expr._subs(x, expr)
                            return self.func(expr, (sym, base_set))
                    
                if self.is_ConditionSet:
    #                 domain = self.limits[0][1]
                    if domain.is_set: 
                        return domain
                    if domain.is_And:
                        for i, eq in enumerate(domain.args):
                            if eq.is_Element and eq.lhs == x:
                                eqs = [*domain.args]
                                del eqs[i]
                                cond = And(*eqs)
                                return self.func[x:cond:eq.rhs](self.expr)
                                
                return self

            if len(limit) > 2: 
                if limit[2].is_set:
                    x, condition, base_set = limit
                    # for condition set:
                    if self.expr == x.set:
                        domain = x.domain_conditioned(condition)
                        if not domain.is_ConditionSet:
                            return domain & base_set
                        
                    if base_set.is_ConditionSet and base_set.variable == x:
                        return self.func[x:condition & base_set.condition:base_set.base_set](self.expr).simplify()
                         
                    if condition.domain_defined(x) & self.expr.domain_defined(x) in base_set:
                        return self.func(self.expr, (x, condition))
                else:
                    x, a, b = limit
                    if a == b - 1:
                        return self.expr._subs(x, a)
                    domain = Range(a, b)
                    if self.expr.is_Piecewise: 
    #                    arr = [arr[-1]] + arr[0:-1]
                        return self.expr.as_multiple_terms(x, domain, self.func).simplify()
                    if self.expr.is_FiniteSet:
                        s = self.expr
                        if len(s) == 1 and x == s.arg:
                            return domain
                    if not self.expr._has(x):
                        return self.expr
                    
                    if self.expr.domain_defined(x) in domain:
                        return self.func(self.expr, (x,))

            if len(limit) == 1:
                x = limit[0]
                if self.expr.is_FiniteSet:
                    if len(self.expr) == 1:
                        element, *_ = self.expr.args
                        if element == x:
                            return x.domain

                if self.expr.is_Piecewise:
                    universe = x.universalSet
                    has_x = [c._has(x) for _, c in self.expr.args[:-1]]                                
                    if not any(has_x):
                        return self.expr.func(*((self.func(e, (x, universe)).simplify(), c) for e, c in self.expr.args)).simplify()
                    
                    if all(has_x):
                        return self.expr.as_multiple_terms(x, universe, self.func).simplify()

                    if has_x[0]:
                        index = has_x.index(False)
                        
                        independent_of_x = []
                        for arg in self.expr.args[index:]: 
                            independent_of_x.append(arg)
                        independent_of_x = self.expr.func(*independent_of_x)

                        dependent_on_x = []
                        for arg in self.expr.args[:index]: 
                            dependent_on_x.append(arg)
                                                
                        dependent_on_x.append((independent_of_x, True))
                        dependent_on_x = self.expr.func(*dependent_on_x)

                        return self.func(dependent_on_x, *self.limits).simplify()                    
                    else: 
                        index = has_x.index(True)
                        dependent_on_x = []
                        for arg in self.expr.args[index:]: 
                            dependent_on_x.append(arg)

                        dependent_on_x = self.expr.func(*dependent_on_x)                    
                        independent_of_x = []
                        for arg in self.expr.args[:index]: 
                            independent_of_x.append(arg)                        
                                                
                        independent_of_x.append((dependent_on_x, True))
                        independent_of_x = self.expr.func(*independent_of_x)

                        return self.func(independent_of_x, *self.limits).simplify()                    
                    return self

        return ExprWithLimits.simplify(self)

    def union_sets(self, expr):
        if expr.is_Complement:
            A, B = expr.args
            if B in self:
                return self | A
        
        if expr.func == self.func:
            if self.expr == expr.expr:
                if self.is_ConditionSet and expr.is_ConditionSet:
                    if self.variable == expr.variable:
                        if self.base_set == expr.base_set: 
                            return conditionset(self.variable, self.condition | expr.condition, self.base_set)
                        if self.condition == expr.condition:
                            return conditionset(self.variable, self.condition, self.base_set | expr.base_set)
                else:
                    limits = self.limits_union(expr)
                    return self.func(self.expr, *limits)

        if self.is_ConditionSet:
            if self.base_set in expr:
                return expr
            return
        
        if len(self.limits) == 1:
            i, *args = self.limits[0]
            if len(args) == 2:
                a, b = args
                if self.expr.subs(i, b) == expr:
                    return self.func(self.expr, (i, a, b + 1))
                if self.expr.subs(i, a - 1) == expr:
                    return self.func(self.expr, (i, a - 1 , b))

                i_ = Wild(i.name)

                dic = expr.match(self.expr.subs(i, i_))
                if dic:
                    i_match = dic[i_]
                    if i_match >= a and i_match <= b:
                        return self

            elif len(args) == 1:
                domain = args[0]
                from sympy import Complement
                if domain.is_Complement:
                    A, B = domain.args
                    if B.is_FiniteSet:
                        deletes = set()
                        expr_set = self.etype.emptySet
                        for b in B:
                            s = self.expr.subs(i, b)
                            if s == expr or s in expr:
                                deletes.add(b)
                                expr_set |= s
                                
                        if deletes:
                            deletes = FiniteSet(*deletes)
                            B = Complement(B, deletes)
                            expr = Complement(expr, expr_set)
                            if B:
                                A = Complement(A, B)
                            this = self.func(self.expr, (i, A)).simplify()
                            if expr.is_EmptySet:
                                return this
                            return this | expr
                    elif B.is_Complement:
# apply: A \ (B \ C) = (A \ B) | (A & B & C)
                        b, c = B.args
                        domain = Complement(A, b)                        
#                         print(A & b & c)
                        assert Complement(A, Complement(b, c)) == Complement(A, b) | (A & b & c)
                        expr |= self.func(self.expr, (i, A & b & c)).simplify()
                        return expr | self.func(self.expr, (i, domain))

    def _sympystr(self, p):
        if self.is_ConditionSet: 
            return 'conditionset(%s)' % ', '.join(p._print(arg) for arg in self.limits[0])
        
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return 'Cup[%s](%s)' % (limits, p._print(self.expr))
        return 'Cup(%s)' % p._print(self.expr)

    def _lean(self, p):
        if self.is_ConditionSet: 
            return 'setOf(%s)' % ', '.join(p._print(arg) for arg in self.limits[0])
        limits = ','.join((limit._format_ineq(p) for limit in self.limits))
        return '\N{N-ARY UNION} %s, %s' % (limits, p._print(self.expr))
    
    def int_limit(self):
        if len(self.limits) == 1:
            limit = self.limits[0]
            if len(limit) == 3 and not limit[2].is_set:
                return limit

    def condition_limit(self):
        if len(self.limits) == 1:
            limit = self.limits[0]
            if len(limit) == 2:
                return limit
            if len(limit) == 3: 
                x, a, b = limit
                if a.is_bool:
                    return x, conditionset(x, a, b)
                return x, x.range(a, b) 
            else:
                x, = limit
                return x, x.universalSet

    def image_set(self):
        expr = self.expr
        if isinstance(expr, FiniteSet) and len(expr) == 1:
            condition_limit = self.condition_limit()
            if condition_limit is not None:
                x, baseset = condition_limit
                expr, = expr
                return x, expr, baseset

    def finite_set(self):
        expr = self.expr
        limit = self.int_limit()
        if limit is None:
            return

        x, a, b = limit
        if isinstance(expr, FiniteSet):
            if len(expr) == 1:
                expr, = expr
                if isinstance(expr, Indexed):
                    if len(expr.indices) == 1:
                        base = expr.base
                    else:
                        base = expr.base[expr.indices[:-1]]
                    diff = expr.indices[-1] - x
                    if diff.has(x):
                        return
                    return base[a + diff: b + diff]

    def _latex(self, p):
        finite_set = self.finite_set()
        if finite_set is not None:
            return p._print(finite_set)

        if self.is_ConditionSet:
            vars_print = p._print(self.variable)
            if self.variable in self.base_set:
                return r"\left\{%s \left| %s \right. \right\}" % (vars_print, p._print(self.condition))
    
            return r"\left\{%s \in %s \left| %s \right. \right\}" % (vars_print, p._print(self.base_set), p._print(self.condition))

        image_set = self.image_set()
        if image_set is not None:
            lamda_variables, lamda_expr, base_set = image_set
            if base_set.is_ConditionSet and lamda_variables == base_set.variable:
                if base_set.variable in base_set.base_set:
                    return r"\left\{%s \left| %s \right. \right\}" % (p._print(lamda_expr), p._print(base_set.condition))
                else:
                    return r"\left\{%s \left| %s \wedge %s \in %s \right. \right\}" % (p._print(lamda_expr), p._print(base_set.condition), p._print(base_set.variable), p._print(base_set.base_set))

            if lamda_variables.is_Tuple:
                varsets = [r"%s \in %s" % (p._print(var), p._print(setv)) for var, setv in zip(lamda_variables, base_set)]
                return r"\left\{%s \left| %s \right. \right\}" % (p._print(lamda_expr), ', '.join(varsets))

            if base_set.is_Boolean:
                varsets = p._print(base_set)
            else:
                varsets = r"%s \in %s" % (p._print(lamda_variables), p._print(base_set))
            return r"\left\{ %s \left| %s \right. \right\}" % (p._print(lamda_expr), varsets)
#             return r"\left\{\left. %s \right| %s \right\}" % (p._print(lamda_expr), varsets)

        expr = self.expr
        limits = self.limits
        tex = r"\bigcup"
        
        if len(limits) == 1:
            limit = limits[0]
            
            if len(limit) == 1:
                tex += r"_{%s} " % p._print(limit[0])
            elif len(limit) == 2:
                x, c = limit
                if c.is_set:
                    tex += r"\limits_{%s \in %s} " % (p._print(x), p._print(c))
                else:
                    tex += r"\limits_{%s \left| %s \right.} " % (p._print(x), p._print(c))
            else:
                x, a, b = limit
                if a.is_Zero and x.is_integer and b.is_symbol:
                    tex += r"\limits_{%s:%s}" % tuple([p._print(s) for s in (x, b)])
                elif b.is_set:
                    tex += r"\limits_{%s \in %s \left| %s \right.} " % (p._print(x), p._print(b), p._print(a))
                else:
                    b -= 1
                    tex += r"\limits_{%s=%s}^{%s} " % (p._print(x), p._print(a), p._print(b))                    
        else:
            if all(len(limit) == 1 for limit in limits):
                tex += r"\limits_{%s} " % str.join(',', [l._format_ineq(p) for l in limits])
            else:
                tex += r"\limits_{\substack{%s}} " % str.join('\\\\', [l._format_ineq(p) for l in limits])

        if expr.is_Add:
            tex += r"\left(%s\right)" % p._print(expr)
        else:
            tex += p._print(expr)

        return tex
    
    def _complement(self, universe):
        # DeMorgan's Law
        if self.is_ConditionSet:
            if self.base_set == universe:
                return ~self
            if universe.is_ConditionSet:
                if self.variable == universe.variable and universe.base_set == self.base_set:
                    return conditionset(self.variable, universe.condition & self.condition.invert(), self.base_set)                    

    def __invert__(self):
        assert self.is_ConditionSet
        condition = self.condition.invert()
        return conditionset(self.variable, condition, self.base_set)

    def invert(self):
        assert self.is_ConditionSet
        condition = self.condition.invert()
        return conditionset(self.variable, condition, self.base_set)

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
        from sympy.sets.contains import Element
        if other.has(*self.variables):
            return
        from sympy import Any
        return Any(Element(other, self.expr), *self.limits)

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
            for set in sets:
                if set[0] in sos_list:
                    continue
                else:
                    sos_list.append(set[0])
                    sets_list.append(set)
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
                from sympy.core.relational import Ne
                return And(Ne(symbol, a.sup), symbol < b.sup, symbol > a.inf)        
        return Or(*[set.as_relational(symbol) for set in self.args])

    @property
    def is_iterable(self):
        return all(arg.is_iterable for arg in self.args)

    def _eval_evalf(self, prec):
        try:
            return Union(*(set._eval_evalf(prec) for set in self.args))
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
            nexts = itertools.cycle(iter(it).__next__ for it in iterables)
            
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

    @property
    def etype(self):
        return self.expr.etype

    def _eval_Card(self):
        if self.is_ConditionSet:
            ...

    def min(self): 
        m = Minima(self.expr.min(), *self.limits)
        m_ = m.doit()
        if m_ is not m:
            m = m_
        return m

    def max(self):
        m = Maxima(self.expr.min(), *self.limits)
        m_ = m.doit()
        if m_ is not m:
            m = m_
        return m

    def _eval_is_extended_integer(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_extended_integer
    
    def _eval_is_super_integer(self):
        return self.expr_within_context.is_super_integer
    
    def _eval_is_extended_rational(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_extended_rational
    
    def _eval_is_hyper_rational(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_hyper_rational
    
    def _eval_is_super_rational(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_super_rational
    
    def _eval_is_extended_real(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_extended_real
    
    def _eval_is_hyper_real(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_hyper_real
    
    def _eval_is_super_real(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_super_real
    
    def _eval_is_extended_complex(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_extended_complex
    
    def _eval_is_hyper_complex(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_hyper_complex
    
    def _eval_is_finiteset(self):
        if self.expr.is_finiteset is None:
            return

        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                if domain.is_bool:
                    return
                if domain.is_set:
                    if domain.is_infiniteset:
                        return
                    _x = x.copy(domain=domain, **x.assumptions0)
                    expr = expr._subs(x, _x)
        return expr.is_finiteset

    def __add__(self, other):
        if other.has(*self.variables) or other.is_set:
            raise Exception("could not add %s, %s" % (self, other))
        
        if self.is_ConditionSet:
            cond = self.condition
            if cond.is_bool:
                variable = self.variable
                baseset = self.base_set
                baseset += other
                cond = cond._subs(variable, variable - other)
                return conditionset(variable, cond, baseset)
                
        return self.func(self.expr + other, *self.limits).simplify()

    @classmethod
    def simplify_Element(cls, self, e, s):
        if s.is_ConditionSet:
            if e == s.variable:
                cond = s.condition
            elif s.variable.is_Sliced:
                cond = s.condition._subs_sliced(s.variable, e)
            else:
                cond = s.condition._subs(s.variable, e)

            return And(cond, self.func(e, s.base_set).simplify())
    
    @classmethod
    def simplify_NotElement(cls, self, e, s):
        if s.is_ConditionSet:
            if e == s.variable:
                cond = s.condition
            elif s.variable.is_Sliced:
                cond = s.condition._subs_sliced(s.variable, e)
            else:
                cond = s.condition._subs(s.variable, e)

            return Or(cond.invert(), self.func(e, s.base_set).simplify())
        
    def _eval_Subset(self, rhs):
        if self.is_ConditionSet:
            sym, condition, base_set = self.variable, self.condition, self.base_set
            if rhs.is_ConditionSet: 
                _sym, _condition, _base_set = rhs.variable, rhs.condition, rhs.base_set
                if sym.type == _sym.type and (base_set == _base_set or base_set in _base_set):
                    if sym != _sym:
                        _condition = _condition._subs(_sym, sym)
                    if condition == _condition:
                        return S.true
                    if condition.is_And:
                        if _condition.is_And and all(eq in condition._argset for eq in _condition.args) or _condition in condition._argset:
                            return S.true
            base_set &= sym.domain
            if base_set in rhs:
                return S.true
        else:
            image_set = self.image_set()
            if image_set is not None:
                _image_set = rhs.image_set()
                if _image_set is not None:
                    x, fx, s = image_set
                    _x, _fx, _s = _image_set
                    if s == _s:
                        if x == _x:
                            if fx == _fx:
                                return S.true
                        else:
                            if fx._subs(x, _x) == _fx:
                                return S.true

    @classmethod
    def identity(cls, self, **_):
        return self.etype.emptySet

    @classmethod
    def is_identity(cls, self, **_):
        return self.is_EmptySet

    @property
    def is_range_stepped(self):
        expr = self.expr
        if expr.is_FiniteSet:
            limits = self.limits
            if len(limits) == 1 and len(expr) == 1:
                [(i, *ab)] = limits
                if not i.is_integer:
                    return
                
                p = expr.arg.as_poly(i)
                if p and p.degree() == 1:
                    if len(ab) == 1:
                        [domain] = ab
                        if domain.is_bool:
                            from sympy import conditionset
                            domain = conditionset(i, domain)
                    elif len(ab) == 2:
                        a, b = ab
                        if b.is_set:
                            return
                        domain = Range(a, b)
                    else:
                        domain = expr.domain_defined(i)
                        
                    return p, domain
                         
    def range_contains(self, s):
        if s.is_FiniteSet:
            range_stepped = self.is_range_stepped
            if not range_stepped:
                return
            
            p, domain = range_stepped
            k = p.nth(1)
            h = p.nth(0)
            from sympy import Element
            
            b = None
            for y in s.args:
                cond = Element((y - h) / k, domain)
                if cond.is_BooleanTrue:
                    _b = True
                elif cond.is_BooleanFalse:
                    _b = False
                else:
                    return
                if b is None:
                    b = _b
                    
                if b != _b:
                    return
            return b

    @classmethod
    def class_key(cls):
        """Nice order of classes. """
        return 6, 2, cls.__name__

    
class Cap(Set, ExprWithLimits):
    """
    Represents an intersection of sets as a :class:`Set`.

    """
    operator = Intersection

    # this will change the default new operator!
    def __new__(cls, expr, *symbols, **assumptions):
        expr = sympify(expr)
        if expr.is_EmptySet or expr.is_UniversalSet:
            return expr
        return ExprWithLimits.__new__(cls, expr, *symbols, **assumptions)

    def _latex(self, p):
        expr = self.expr
        limits = self.limits

        tex = r'\bigcap'
        if len(limits) == 1:
            limit = limits[0]
            if len(limit) == 1:
                tex += r"_{%s} " % p._print(limit[0])
            elif len(limit) == 2:
                tex += r"\limits_{%s \in %s} " % tuple([p._print(i) for i in limit])
            else:
                x, a, b = limit
                tex += r"\limits_{%s=%s}^{%s} " % tuple([p._print(i) for i in (x, a, b - 1)])
        else:
            if all(len(limit) == 1 for limit in limits):
                tex += r"\limits_{%s} " % str.join(',', [l._format_ineq(p) for l in limits])
            else:
                tex += r"\limits_{\substack{%s}} " % str.join('\\\\', [l._format_ineq(p) for l in limits])

        if expr.is_Add:
            tex += r"\left(%s\right)" % p._print(expr)
        else:
            tex += p._print(expr)

        return tex

    @property
    def is_iterable(self):
        return any(arg.is_iterable for arg in self.args)

    def _contains(self, other):
        from sympy.sets.contains import Element
        if other.has(*self.variables):
            return
        from sympy import All
        return All(Element(other, self.expr), *self.limits)

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
        from sympy.core.logic import fuzzy_and, fuzzy_bool
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

        res = FiniteSet(*res, evaluate=False) if res else s.etype.emptySet
        if unk:
            symbolic_s_list = [x for x in s if x.has(Symbol)]
            non_symbolic_s = s - FiniteSet(*symbolic_s_list, evaluate=False)
            while fs_args:
                v = fs_args.pop()
                if all(i == j for i, j in zip_longest(symbolic_s_list, (x for x in v if x.has(Symbol)))):
                    # all the symbolic elements of `v` are the same
                    # as in `s` so remove the non-symbol containing
                    # expressions from `unk`, since they cannot be
                    # contained
                    for x in non_symbolic_s:
                        if x in unk:
                            unk.remove(x)
                else:
                    # if only a subset of elements in `s` are
                    # contained in `v` then remove them from `v`
                    # and add this as a new arg
                    contained = [x for x in symbolic_s_list if sympify(v.contains(x)) is S.true]
                    if contained != symbolic_s_list:
                        other.append(v - FiniteSet(*contained, evaluate=False))
                    else:
                        pass  # for coverage

            other_sets = Intersection(*other)
            if not other_sets:
                return s.etype.emptySet  # b/c we use evaluate=False below
            elif other_sets.is_UniversalSet:
                res += FiniteSet(*unk)
            else:
                res += Intersection(FiniteSet(*unk), other_sets, evaluate=False)
        return res

    def as_relational(self, symbol):
        """Rewrite an Intersection in terms of equalities and logic operators"""
        return And(*[s.as_relational(symbol) for s in self.args])

    """
    precondition: this set should not be empty!
    """

    def min(self): 
        return Maxima(self.expr.min(), *self.limits)        

    """
    precondition: this set should not be empty!
    """

    def max(self):
        return Minima(self.expr.max(), *self.limits)

    # finiteness of intersection set is hard to evaluate
    def _eval_is_finiteset(self):
        if self.expr.is_finiteset is None:
            return
        
        if self.expr.is_finiteset == True:
            return True

        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_finiteset

    def _eval_is_extended_integer(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_extended_integer
    
    def _eval_is_super_integer(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_super_integer
    
    def _eval_is_extended_rational(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_extended_rational
    
    def _eval_is_hyper_rational(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_hyper_rational
    
    def _eval_is_super_rational(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_super_rational
    
    def _eval_is_extended_real(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_extended_real
    
    def _eval_is_hyper_real(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_hyper_real
    
    def _eval_is_super_real(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_super_real
    
    def _eval_is_extended_complex(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_extended_complex
    
    def _eval_is_hyper_complex(self):
        expr = self.expr
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and domain and domain.is_set:
                _x = x.copy(domain=domain)
                expr = expr._subs(x, _x)
        return expr.is_hyper_complex
    
    def simplify(self, deep=False, **kwargs):
        if deep:
            _self = ExprWithLimits.simplify(self, deep=True)
            if _self != self:
                return _self

        if len(self.limits) == 1:
            limit, = self.limits
            if len(limit) == 2: 
                from sympy.core.relational import Unequal
                x, domain = limit

                if not self.expr._has(x):
                    if domain.is_bool:
                        from sympy import conditionset
                        domain = conditionset(x, domain).simplify()
                    return Piecewise((self.expr, Unequal(domain, x.emptySet).simplify()), (self.expr.etype.universalSet, True)).simplify()

                if domain.is_FiniteSet and len(domain) == 1:
                    return self.finite_aggregate(x, domain)

                if domain.is_EmptySet:
                    return self.expr.etype.universalSet

                if domain.is_Intersection:
                    args = []
                    success = False
                    for dom in domain.args:
                        arg = self.func(self.expr, (x, dom)).simplify()
                        args.append(arg)
                        if not arg.is_Cap or arg.expr != self.expr:
                            success = True
                    if success:
                        return Intersection(*args)

                if domain.is_Range:
                    return self.func(self.expr, (x, domain.min(), domain.max() + 1))

                if self.expr.is_Complement:
                    A, B = self.expr.args
                    if not B.has(*self.variables):
                        return self.func(A, *self.limits) // B

                if domain.is_Piecewise:
                    tuples = []
                    for e, c in domain.args: 
                        tuples.append((self.func(self.expr, (x, e)).simplify(), c))    
                    return domain.func(*tuples)
                if domain.is_bool:
                    if domain.is_Equal:
                        if domain.lhs == x:
                            return self.expr._subs(x, domain.rhs)
                        elif domain.rhs == x:
                            return self.expr._subs(x, domain.lhs)
                    elif domain.is_Element:
                        if domain.lhs == x:
                            return self.func(self.expr, (x, domain.rhs))

                if domain.is_set:
                    if not domain.is_symbol:
                        image_set = domain.image_set()
                        if image_set:
                            expr, sym, base_set = image_set
                            expr = self.expr._subs(x, expr)
                            return self.func(expr, (sym, base_set))

                if self.is_ConditionSet:
    #                 domain = self.limits[0][1]
                    if domain.is_set: 
                        return domain
                    if domain.is_And:
                        for i, eq in enumerate(domain.args):
                            if eq.is_Element and eq.lhs == x:
                                eqs = [*domain.args]
                                del eqs[i]                            
                                cond = And(*eqs)
                                return self.func[x:cond:eq.rhs](self.expr)

                return self
            
            if len(limit) == 3:
                x, a, b = limit
                if a == b - 1:
                    return self.expr._subs(x, a)
                
                domain = Range(a, b)
                if self.expr.is_FiniteSet:
                    s = self.expr
                    if len(s) == 1 and x == s.arg:
                        return domain
                if not self.expr._has(x):
                    return self.expr
                
                if self.expr.domain_defined(x) in domain:
                    return self.func(self.expr, (x,))

        return ExprWithLimits.simplify(self)

    def intersection_sets(self, expr):
        
        if expr.func == self.func:
            if self.expr == expr.expr:
                limits = self.limits_union(expr)
                return self.func(self.expr, *limits)
            else:
                return

        if len(self.limits) == 1:
            i, *args = self.limits[0]
            if len(args) == 2:
                a, b = args
                if self.expr.subs(i, b) == expr:
                    return self.func(self.expr, (i, a, b + 1))
                if self.expr.subs(i, a - 1) == expr:
                    return self.func(self.expr, (i, a - 1 , b))

                i_ = Wild(i.name)

                dic = expr.match(self.expr.subs(i, i_))
                if dic:
                    i_match = dic[i_]
                    if i_match >= a and i_match <= b:
                        return self

    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return 'Cap[%s](%s)' % (limits, p._print(self.expr))
        return 'Cap(%s)' % p._print(self.expr)

    def _lean(self, p):
        limits = ','.join((limit._format_ineq(p) for limit in self.limits))
        return '\N{N-ARY INTERSECTION} %s, %s' % (limits, p._print(self.expr))
    
    @property
    def etype(self):
        return self.expr.etype

    def __add__(self, other):
        if other.has(*self.variables) or other.is_set:
            raise Exception("could not add %s, %s" % (self, other))
        
        return self.func(self.expr + other, *self.limits).simplify()

    @classmethod
    def identity(cls, self, **_):
        return self.etype.universalSet

    @classmethod
    def is_identity(cls, self, **_):
        return self.is_UniversalSet

    @classmethod
    def class_key(cls):
        """Nice order of classes. """
        return 6, 1, cls.__name__
