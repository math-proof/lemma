from sympy.logic.boolalg import Boolean, And, Or
from sympy.concrete.quantifier import Quantifier
from sympy.sets.sets import FiniteSet
from sympy.concrete.expr_with_limits import ExprWithLimits
from sympy.core.relational import Unequal
from sympy.core.sympify import sympify
from sympy.core.singleton import S

class Exists(Quantifier):
    """
    Any[x:A] q(x) <=> conditionset(x, q(x), A) != EmptySet
    """
    
    operator = Or
    
    # this will change the default new operator!
    def __new__(cls, expr, *symbols, **assumptions):
        evaluate = assumptions.pop('evaluate', True)
        if assumptions:
            from sympy.core.inference import Inference
            return Inference(Exists.__new__(cls, expr, *symbols, evaluate=evaluate), **assumptions)
        
        expr = sympify(expr)
        if expr.is_BooleanAtom or len(symbols) == 0:
            return expr.copy(**assumptions)
        return ExprWithLimits.__new__(cls, expr, *symbols, evaluate=evaluate, **assumptions)
    
    def subs(self, *args, **kwargs):
        if all(isinstance(arg, Boolean) for arg in args):
            if 'var' in kwargs:
                assert len(args) == 0
                args = [self.limits_dict[kwargs.pop('var')]]

            if len(args) == 1:
                eq, *_ = args
                if self.expr.is_And:
                    if eq in self.expr.args:
                        expr = self.expr.subs(eq)
                        clue = expr.clue
                        
                        kwargs.clear()
                        kwargs[clue] = self
                        return self.func(expr, *self.limits, **kwargs).simplify()
                    
        return Quantifier.subs(self, *args, **kwargs)

    def simplify(self, **kwargs):
        from sympy.sets.contains import Element, NotElement
        if self.expr.is_Equal:
            limits_dict = self.limits_dict
            x = None
            if self.expr.lhs in limits_dict:
                x = self.expr.lhs
                y = self.expr.rhs
            elif self.expr.rhs in limits_dict:
                x = self.expr.rhs
                y = self.expr.lhs

            if x is not None and not y.has(x):
                domain = limits_dict[x]
                assert not isinstance(domain, list)
                if domain is None:
                    if len(self.limits) == 1:
                        if all(not var.is_given for var in y.free_symbols):
                            domain_bounded = x.domain_bounded
                            if domain_bounded is None:
                                return Element(y, x.domain).simplify()
                            
                            if y.domain in domain_bounded:
                                return S.BooleanTrue
                elif domain.is_set:
                    t = self.variables.index(x)
                    if not any(limit._has(x) for limit in self.limits[:t]):
                        expr = Element(y, domain)
                        if expr:
                            return expr
                        limits = self.limits_delete(x)
                        if limits:
                            return self.func(expr, *limits)
                        return expr
        
        if self.expr.is_Element: 
            limits_dict = self.limits_dict
            x = None
            if self.expr.lhs in limits_dict:
                x = self.expr.lhs
                S = self.expr.rhs
            
            if x is not None:
                domain = limits_dict[x]
                if domain is None or isinstance(domain, list):
                    return self
                
                if domain.is_set:
                    if domain.is_FiniteSet:
                        expr = Element(domain.arg, S)
                    else:
                        expr = Unequal(S & domain, x.emptySet)
                else:
                    expr = None
                
                if expr is not None:
                    limits = self.limits_delete((x,))
                    if limits:
                        return self.func(expr, *limits).simplify()
                    else:
                        if expr.is_BooleanAtom:
                            return expr
                        return expr

        elif self.expr.is_NotElement: 
            limits_dict = self.limits_dict
            x = None
            if self.expr.lhs in limits_dict:
                x = self.expr.lhs
                S = self.expr.rhs
                
            if x is not None:
                domain = limits_dict[x]
                if isinstance(domain, list):
                    from sympy import Equal
                    expr = Equal(S, x.emptySet)
                elif domain.is_set:
                    if domain.is_FiniteSet:
                        expr = NotElement(domain.arg, S)
                    else:
                        expr = Unequal(domain // S, x.emptySet)                        
                else:
                    expr = None
                
                if expr is not None:
                    limits = self.limits_delete((x,))
                    if limits:
                        return self.func(expr, *limits).simplify()
                    else:
                        if expr.is_BooleanAtom:
                            return expr
                        return expr
                    
        if self.expr.is_And:
            limits_dict = self.limits_dict
            for i, eq in enumerate(self.expr.args):
                if eq.is_Element and eq.lhs in limits_dict:
                    domain = limits_dict[eq.lhs]
                    if domain is None:
                        eqs = [*self.expr.args]
                        del eqs[i]  
                        if not eq.rhs.has(*self.variables[:i]):
                            return self.func(And(*eqs), *self.limits_update(eq.lhs, eq.rhs)).simplify()
                    elif domain == eq.rhs:
                        eqs = [*self.expr.args]
                        del eqs[i]
                        return self.func(And(*eqs), *self.limits)

                if eq.is_Equal: 
                    if eq.lhs in limits_dict:
                        old, new = eq.args
                    elif eq.rhs in limits_dict:
                        new, old = eq.args
                    else:
                        continue
                    
                    continue
                
        if self.expr.is_Or:
            limits_dict = self.limits_dict
            for i, eq in enumerate(self.expr.args):
                if eq.is_NotElement and eq.lhs in limits_dict:
                    domain = limits_dict[eq.lhs]
                    if not isinstance(domain, list) and domain and domain in eq.rhs:
                        eqs = [*self.expr.args]
                        del eqs[i]
                        return self.func(And(*eqs), *self.limits)

        return Quantifier.simplify(self, **kwargs)

    def union_sets(self, expr):
        if len(self.limits) == 1:
            i, *args = self.limits[0]
            if len(args) == 2:
                a, b = args
                if self.expr.subs(i, b + 1) == expr:
                    return self.func(self.expr, (i, a, b + 1))
                if self.expr.subs(i, a - 1) == expr:
                    return self.func(self.expr, (i, a - 1 , b))

    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        return 'Any[%s](%s)' % (limits, p._print(self.expr))

    def _lean(self, p):
        return All._lean(self, p, '\N{THERE EXISTS}')

    def _pretty(self, p):
        return Quantifier._pretty(self, p, '\N{THERE EXISTS}')
    
    def int_limit(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        if len(limit) == 3:
            return limit

    def condition_limit(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        if len(limit) == 2:
            return limit

    def expr_iterable(self):
        expr = self.expr

        if isinstance(expr, FiniteSet):
            if len(expr) == 1:
                expr, *_ = expr
                if expr.is_Indexed:
                    if len(expr.indices) == 1:
                        return expr.base
                    return expr.base[expr.indices[:-1]]

    latexname = 'exists'
    
    def __or__(self, eq):
        """Overloading for | operator"""
        if eq.is_Exists:
            if self.limits == eq.limits:
                return self.func(self.expr | eq.expr, *self.limits)
                        
            if self.expr == eq.expr:
                limits = self.limits_union(eq)
                return self.func(self.expr, *limits).simplify()
        
        return Quantifier.__or__(self, eq)

    @classmethod
    def simplify_ForAll(cls, self, exists, *limits):
        if exists.expr.is_ForAll:
            forall = exists.expr
            dic = self.limits_common(forall)
            if dic:
                forall = forall.func(forall.expr, *forall.limits_update(dic))
                exists = exists.func(forall, *exists.limits)

                return self.func(exists, *limits_delete(limits, dic))
        
    def apply(self, axiom, *args, **kwargs):
        for arg in args:
            if isinstance(arg, tuple):
                x, *_ = arg
                from sympy import Basic
                if isinstance(x, Basic) and x.is_symbol:
                    if x in self.variables_set:
                        print('variables are given in Any context!')
                        return self
        
        return Quantifier.apply(self, axiom, *args, **kwargs)

    def reduced_cond(self, x, cond, baseset=None):
        if baseset:
            return self.func[x:baseset](cond)
        if cond.is_set:
            return Unequal(cond, x.emptySet)
        return self.func[x](cond)

    @property
    def canonical(self):
        return self

    @classmethod
    def identity(cls, self, **kwargs):
        return S.false.copy(**kwargs)

    @classmethod
    def is_identity(cls, self):
        return self.is_BooleanFalse


from sympy.concrete.forall import All
Any = Exists
Any.invert_type = All
All.invert_type = Any

from sympy.concrete.limits import *
