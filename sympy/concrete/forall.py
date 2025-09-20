from sympy.logic.boolalg import Boolean, And, Or
from sympy.concrete.expr_with_limits import ExprWithLimits
from sympy.concrete.quantifier import Quantifier
from sympy.core.sympify import sympify
from sympy.core.relational import Equal
from sympy.core.singleton import S

class ForAll(Quantifier):
    """
    All[p] q <=> !p | q
    """
    
    operator = And

    # this will change the default new operator!
    def __new__(cls, expr, *symbols, **assumptions):
        evaluate = assumptions.pop('evaluate', True)
        if assumptions:
            from sympy.core.inference import Inference
            return Inference(ForAll.__new__(cls, expr, *symbols, evaluate=evaluate), **assumptions)
        
        expr = sympify(expr)
        if expr.is_BooleanAtom or len(symbols) == 0:
            if not expr:
                eqs = []
                for _, *ab in symbols:
                    if len(ab) == 1:
                        domain = ab[0]
                        if domain.is_set:
                            eqs.append(Equal(domain, domain.etype.emptySet))
                        elif domain.is_bool:
                            eqs.append(domain.invert())
                if eqs:
                    return And(*eqs, evaluate=evaluate, **assumptions)
            return expr.copy(**assumptions)
        return ExprWithLimits.__new__(cls, expr, *symbols, evaluate=evaluate, **assumptions)

    def subs(self, *args, **kwargs):
        if all(isinstance(arg, Boolean) for arg in args):
            return Quantifier.subs(self, *args, **kwargs)
        old, new = args
        if old.is_Sliced:
            return self._subs_sliced(old, new)
        new = sympify(new)        
        if old in self.variables:
            wrt, *ab = self.limits[self.variables.index(old)]
            if len(ab) == 1:
                domain = ab[0]
            else:
                a, b = ab
                if b.is_set:
                    domain = b & old.domain_conditioned(a)
                else:
                    domain = wrt.range(a, b)

            eqs = []
            if not domain.is_set:
                domain = old.domain_conditioned(domain)

            from sympy.sets.contains import NotElement
            limit_cond = NotElement(new, domain).simplify()
            eqs.append(limit_cond)

            if self.expr.is_Or:
                for equation in self.expr.args:
                    eqs.append(equation._subs(old, new))
            else:
                eqs.append(self.expr._subs(old, new))

            limits = self.limits_delete(old)
            if limits:
                for i, (x, *ab) in enumerate(limits):
                    if ab:
                        limits[i] = (x, *(expr._subs(old, new) for expr in ab))  
                            
                return self.func(Or(*eqs), *limits, given=self)
            else:
                return Or(*eqs, given=self).simplify()
                
        return Quantifier.subs(self, *args, **kwargs)
        
    def simplify(self, **kwargs):
        local = kwargs.get('local')
        deletes = []
        for i in range(len(self.limits) - 1, -1, -1):
            x, *ab = self.limits[i]
            if not ab and not local:
                deletes.append(x)
                continue
            if len(ab) == 1:
                domain = ab[0]
            elif ab:
                a, b = ab
                if b.is_set:
                    continue
                domain = x.range(a, b)
            else:
                domain = x.universalSet
                
            if self.expr._has(x) and domain.is_set:
                _eval_domain_defined = self.expr.domain_defined(x)
                if _eval_domain_defined in domain and not local:
                    deletes.append(x)
                domain &= _eval_domain_defined
                if domain.is_FiniteSet:
                    if len(domain) == 1:
                        x0, *_ = domain
                        expr = self.expr._subs(x, x0)
                        if expr.is_BooleanAtom:
                            return expr
                        
                        limits = [*self.limits]
                        del limits[i]
                        for j in range(i):
                            limits[j] = limits[j]._subs(x, x0)
                             
                        if limits:
                            return self.func(expr, *limits)
                        else:
                            return expr.simplify()

        if deletes:
            limits = self.limits_delete(deletes)
            if limits:
                return self.func(self.expr, *limits).simplify()

            if local:
                limits = [(x,) for x, *_ in self.limits if self.expr._has(x)]
                return self.func(self.expr, *limits)
            return self.expr

        this = self.expr.func.simplify_ForAll(self, *self.args)
        if this is not None:
            return this

        return Quantifier.simplify(self, **kwargs)
        
    def simplify_int_limits(self, expr):
        for i, domain in self.limits_dict.items():
            if not i.is_integer or i.shape or isinstance(domain, Boolean):
                continue

            i_expr = []
            patterns = []
            non_i_expr = set()
            from sympy import Wild
            _i = Wild('_i', **i.type.dict)
            for eq in expr.args:
                if eq._has(i):
                    i_expr.append(eq)
                    patterns.append(eq._subs(i, _i))
                else:
                    non_i_expr.add(eq)

            matched_dic = {}
            for eq in non_i_expr:
                for pattern in patterns:
                    res = eq.match(pattern)
                    if not res:
                        continue

                    t, *_ = res.values()
                    if t in matched_dic:
                        matched_dic[t].add(eq)
                    else:
                        matched_dic[t] = {eq}
                    break

            new_set = set()
            for t, eqs in matched_dic.items():
                if len(eqs) != len(non_i_expr):
                    continue
                non_i_expr -= eqs
                new_set.add(t)

            if not new_set:
                continue

            eqs = i_expr + [*non_i_expr]

            limits = self.limits_update(i, domain | new_set)                
            
            expr = expr.func(*eqs)
            return expr, limits
    
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
        return 'All[%s](%s)' % (limits, p._print(self.expr))

    def _lean(self, p, operator='\N{FOR ALL}'):
        limits = [limit._format_ineq(p) for limit in self.limits]
        if all(len(limit) == 1 for limit in self.limits):
            operator += "".join(' ' + limit for limit in limits)
        else:
            operator = ", ".join(reversed(["%s %s" % (operator, limit) for limit in limits]))
        operator = operator.replace('%', '%%')
        return f'{operator}, %s' % p._print(self.expr)

    def _pretty(self, p):
        return Quantifier._pretty(self, p, '\N{FOR ALL}')

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

    def __and__(self, eq):
        """Overloading for & operator"""
        if eq.is_ForAll: 
            if self.expr == eq.expr:
                limits = self.limits_union(eq)
                return self.func(self.expr, *limits).simplify()

            if self.limits == eq.limits:
                return All(self.expr & eq.expr, *self.limits)                
                                                    
        for i, (x, *ab) in enumerate(self.limits):
            if len(ab) == 1:
                cond, *_ = ab
                if cond.is_Unequal:
                    invert = cond.invert()
                    if self.expr._subs(*invert.args) == eq:
                        limits = [self.limits]
                        del limits[i]                        
                        return self.func(self.expr, *limits).simplify()                        
                    
        return Quantifier.__and__(self, eq)

    def apply(self, axiom, *args, **kwargs):
        for arg in args:
            if isinstance(arg, tuple):
                x, *_ = arg
                from sympy import Basic
                if isinstance(x, Basic) and x.is_symbol:
                    if x in self.free_symbols:
                        return self
                    elif x in self.variables_set:
                        index = self.variables.index(x)
                        x, domain = Tuple.as_setlimit(arg)
                        x, domain_given = Tuple.as_setlimit(self.limits[index])
                        if domain.is_set and domain_given.is_set:
                            if domain in domain_given:
                                ...
                            else:
                                print("variables' are beyond the bound given in All context!")
                                return self
        
        return Quantifier.apply(self, axiom, *args, **kwargs)    

    def inference_status(self, child):
        return child > 0

    def reduced_cond(self, x, cond, baseset=None):
        if baseset:
            return self.func.invert_type[x:baseset](cond.invert())
        if cond.is_set:
            return Equal(cond, x.emptySet)
        return self.func.invert_type[x](cond.invert())
    
    @classmethod
    def identity(cls, self, **kwargs):
        return S.true.copy(**kwargs)

    @classmethod
    def is_identity(cls, self):
        return self.is_BooleanTrue

    latexname = 'forall'


from sympy.concrete.limits import *

All = ForAll