"""
----
at present Inference is mainly needed for process of theorem proof
"""
from sympy.logic.invoker import Invoker
from sympy.logic.boolalg import And
from sympy.sets.sets import conditionset, imageset
from sympy.core.basic import Basic


class Inference:
    is_Inference = True
    _op_priority = 20
    
    def __init__(self, cond, **_assumptions):
        self.cond = cond.cond if cond.is_Inference else cond
        self._assumptions = _assumptions

    def __getattr__(self, attr):
        return getattr(self.cond, attr)

    @property
    def T(self):
        return Inference(self.cond.T, equivalent=self)

    @property
    def equivalent(self):
        return self._assumptions.get('equivalent')
    
    @equivalent.setter
    def equivalent(self, eq):
        if eq is not None:
            assert 'equivalent' not in self._assumptions
            assert not self.is_BooleanFalse and not self
            assert self is not eq
            self._assumptions['equivalent'] = eq
            if 'plausible' in self._assumptions:
                del self._assumptions['plausible']
            return

        if 'equivalent' in self._assumptions:
            del self._assumptions['equivalent']
    
    @property
    def given(self):
        return self._assumptions.get('given')
    
    @given.setter
    def given(self, eq):
        if eq is not None:
            assert self is not eq
            self._assumptions['given'] = eq
            if 'plausible' in self._assumptions:
                del self._assumptions['plausible']
            
            return

        if 'given' in self._assumptions:
            del self._assumptions['given']
    
    @property
    def imply(self):
        return self._assumptions.get('imply')
    
    @imply.setter
    def imply(self, eq):
        if eq is not None:
            assert self is not eq
            self._assumptions['imply'] = eq
            return

        if 'imply' in self._assumptions:
            del self._assumptions['imply']

# here we define negation = counterproposition
    @property
    def negation(self):
        return self._assumptions.get('negation')
    
    @negation.setter
    def negation(self, eq):
        if eq is not None:
            assert 'negation' not in self._assumptions
            self._assumptions['negation'] = eq
            return

        if 'negation' in self._assumptions:
            del self._assumptions['negation']
    
    def plausibles_set(self, clue='given'):
        find_plausibles = self.find_plausibles(clue=clue)        
        result = [*zip(*find_plausibles)]
        if result:
            plausibles_set, is_equivalent = result
            return {*plausibles_set}, all(is_equivalent)
        return set(), False

    def set_equivalence_relationship(self, other):
        plausibles_set, is_equivalent = self.plausibles_set()
        if len(plausibles_set) == 1:
            if is_equivalent:
                eq, *_ = plausibles_set
                if isinstance(other, (list, tuple)):
                    is_equivalent = True
                    plausibles_set = set()
                    for other in other:
                        _plausibles_set, _is_equivalent = other.plausibles_set()
                        plausibles_set |= _plausibles_set
                        is_equivalent &= _is_equivalent
                else:
                    plausibles_set, is_equivalent = other.plausibles_set()
                
                assert eq not in plausibles_set, 'cyclic proof detected'
                    
                equivalent = [*plausibles_set]
                if len(equivalent) == 1:
                    equivalent, *_ = equivalent
                elif not equivalent:
                    return
                
                if is_equivalent:
                    from sympy.core.compatibility import default_sort_key
                    if isinstance(equivalent, (list, tuple)):
                        p, *q = sorted((eq, *equivalent), key=lambda inf: default_sort_key(inf.cond))                    
                    else:
                        p, q = sorted((eq, equivalent), key=lambda inf: default_sort_key(inf.cond))
                    p.equivalent = q
                else:
                    del eq._assumptions['plausible']
                    eq.given = equivalent
                return True
            else:
                eq, *_ = plausibles_set
                if isinstance(other, list):
                    plausibles_set = set()
                    for other in other:
                        _plausibles_set, is_equivalent = other.plausibles_set()
                        plausibles_set |= _plausibles_set
                        if not is_equivalent:
                            return
                else:
                    plausibles_set, is_equivalent = other.plausibles_set()
                    if not is_equivalent:
                        return
                
                assert eq not in plausibles_set, 'cyclic proof detected'
                    
                equivalent = [*plausibles_set]
                if len(equivalent) == 1:
                    equivalent, *_ = equivalent
                elif not equivalent:
                    return
                
                del eq._assumptions['plausible']
                eq.given = equivalent
                return True
        
    def find_plausibles(self, is_equivalent=True, clue='given'):
        if self._assumptions.get('plausible'): 
            yield self, is_equivalent
        else:
            equivalent = self.equivalent
            if equivalent is None:
                given = getattr(self, clue)
                is_equivalent = False
            else:
                given = equivalent
    
            if given is not None:
                if isinstance(given, (tuple, list, set)): 
                    for given in given:
                        if given.is_Inference:
                            yield from given.find_plausibles(is_equivalent, clue=clue)
                else:
                    if given.is_Inference:
                        yield from given.find_plausibles(is_equivalent, clue=clue)        
                        
    def subs_assumptions_for_equality(self, eq, result, simplify=True):
        if eq.plausible:
            if self.plausible: 
                assumptions = {'given': [self, eq]}
            else:
                assumptions = {'given': eq}
        else:
            if self.plausible:
                result &= self.domain_definition()
                
            assumptions = {'equivalent': self}
        self = result.copy(**assumptions)
        if simplify:
            self = self.simplify()
        return self
    
    def __bool__(self):
        return bool(self.cond)

    def __str__(self):
        return str(self.cond)
    
    __repr__ = __str__
    
    @property
    def this(self):
        return Invoker(self)
    
    @property
    def clue(self):
        if self._assumptions:
            clue, *_ = self._assumptions.keys()
            if clue != 'plausible':
                return clue
    
    def apply(self, axiom, *args, split=True, **kwargs):
        if self.is_And:
            token = axiom.__name__.split(sep='.')
            from sympy.logic.boolalg import inference_type, split_and
            i, type = inference_type(token)
            if type == 'of':
                split = split_and(axiom)
            elif type == 'Is' or axiom.__name__.split(sep='.', maxsplit=3)[2] == 'And':
                split = False
                
            if split: 
                _args = []
                funcs = []
                
                depth = kwargs.pop('depth', None)
                if not depth:
                    _args = [*self.args]
                else:
    
                    def instantiate(eq):
                        function = eq
                        for _ in range(depth):
                            function = function.expr
                        return function
                    
                    for eq in self.args: 
                        if eq.is_Quantifier:
                            _funcs, function = eq.funcs()
                            _funcs = _funcs[-depth:]
                            if funcs:
                                assert _funcs == funcs
                            else: 
                                funcs = _funcs
                            function = instantiate(eq)
                            _args.append(function)
                        else:
                            _args.append(eq)
                            
                function = axiom.apply(*_args, *args, **kwargs)
                if isinstance(function, tuple):
                    for f in function:
                        clue = f.clue
                        break

                    function = And(*function, **{clue: self})                    
                else: 
                    clue = function.clue
                    
                for func, limits in funcs:
                    function = func(function, *limits)
                
                if function.is_BooleanAtom:
                    return function.copy(**{clue: self})
                
                function.set_clause(clue, self, force=True)
                
                if kwargs.get('simplify', True):
                    function = function.simplify()
                return function
        
        eqs = axiom.apply(self, *args, **kwargs)
        if eqs is None:
            return
        if isinstance(eqs, (list, tuple)):
            eqs = And(*eqs, equivalent=eqs)
        elif eqs.is_Equivalent:
            if eqs.clue is None:
                if self.cond is eqs.lhs:
                    return eqs.rhs
        return eqs
    
    @property
    def plausible(self):
#         plausible = True, meaning, the statement is plausibly True, ready to be proven
#         plausible = False, meaning, the statement is proven False
#         plausible = None, meaning, the statement is proven True

        if 'plausible' in self._assumptions:
            return self._assumptions['plausible']

        if self:
            return
        if self.is_BooleanFalse:
            return False

        equivalent = self.equivalent
        if equivalent is not None:
            if isinstance(equivalent, (tuple, list)):
                for parent in equivalent:
                    if parent.plausible:
                        return True
    
                return
            return equivalent.plausible
    
        given = self.given
        if given is not None:
            if isinstance(given, (tuple, list, set)):
                for parent in given:
                    assert parent is not self, self
                    if parent.plausible:
                        return True

                return
            if given.plausible is not None:
#             if self is given by a False / plausible proposition, then self is plausible
                return True
            return
        
        imply = self.imply
        if imply is not None:
#             if self implies a False proposition, then self must be False
            if (plausible := imply._assumptions.get('plausible')) is False:
                return False
            
            if (negation := imply.negation) is not None:
#             if imply.negation implies a True proposition, then self must be False
                if negation.plausible is None:
                    return False

            return True
        
        negation = self.negation
        if negation is not None:
            plausible = negation.plausible
            if plausible is True:
                return True
            if plausible is False:
                return
            return False

    @plausible.setter
    def plausible(self, value):
        if value:
            # this axiom is plausible to be true!
            if 'plausible' in self._assumptions:
                del self._assumptions['plausible']
        else:
            # this axiom is plausible to be false!
            self._assumptions['plausible'] = False

        equivalent = self.equivalent
        if equivalent is not None:
            self.equivalent = None
            process_equivalent(equivalent, value)
            return

        imply = self.imply
        if imply is not None:
            self.imply = None
            process_imply(imply, value)
            return
        
        negation = self.negation
        if negation is not None:
            self.negation = None
            process_negation(negation, value)
            return
        
        given = self.given
        if given is not None:
            self.given = None
            process_given(given, value)
            return

    def __neg__(self):
        cond = -self.cond
        return Inference(cond, equivalent=self)
    
    def doit(self, *args, **kwargs):
        cond = self.cond.doit(*args, **kwargs)
        return Inference(cond, equivalent=self)
    
    def __invert__(self):
        """Return the negated relationship.
        This works more or less identical to ``~``/``Not``. The difference is
        that ``negated`` returns the relationship even if `evaluate=False`.
        Hence, this is useful in code when checking for e.g. negated relations
        to exisiting ones as it will not be affected by the `evaluate` flag.
        """
        invert = self.cond.invert()
        limits_exists = self.cond.limits_exists()
        invert |= self.domain_definition().invert()
        
        if limits_exists:
            from sympy import Any
            return Any(invert, *limits_exists, negation=self).simplify()
        
        return Inference(invert, negation=self)

    def simplify(self, emplace=False, **kwargs):
        cond = self.cond.simplify(**kwargs)
        if cond != self.cond:
            if emplace:
                return Inference(cond, **self._assumptions)
            return Inference(cond, equivalent=self)
        return self
    
    def limits_subs(self, *args, **kwargs):
        cond = self.cond.limits_subs(*args, **kwargs)
        if cond != self.cond:
            return Inference(cond, equivalent=self)
        return self
    
    def subs(self, *args, **kwargs): 
        if 'simplify' not in kwargs:
            kwargs['simplify'] = True

        if all(eq.is_Equal or eq.is_Equivalent for eq in args):
            for eq in args:
                old, new = eq.args
                 
                if self.plausible: 
                    if eq.plausible:
                        cond = self.cond._subs(old, new, **kwargs)
                        if cond == self.cond:
                            continue
                        self = Inference(cond, given=(self, eq))
                    else:
                        if self.is_Or:
                            eqs = []
                            for eq in self.args:
                                eqs.append(eq._subs(old, new) & eq.domain_definition())
                                
                            self = self.func(*eqs).copy(equivalent=self)
                        else:
                            cond = self.cond._subs(old, new, **kwargs)
                            if cond == self.cond:
                                continue

                            cond &= self.domain_definition()
                            self = Inference(cond, equivalent=self)
                else:
                    cond = self.cond._subs(old, new, **kwargs)
                    if cond == self.cond:
                        continue
                    
                    if eq.plausible:
                        self = Inference(cond, given=eq)
                    else:
                        self = Inference(cond, plausible=None)
                    
            return self
            
        old, new = args
        if not old.is_symbol:
            return self
        
        new = sympify(new)
        
        if self.plausible and new._has(old) and old.is_given is False: 
            # used in mathematical induction
            cond = self._subs(old, new, **kwargs)
            return Inference(cond, plausible=True)
        
        if new in old.domain:
            if self.is_Quantifier:
                assert old not in self.variables, 'not supported in built-in axioms, please employ proved theorems: algebra.all.then.cond.subs.apply(...)'
                function = self.expr._subs(old, new, **kwargs)
                limits = []
                for x, *ab in self.limits:
                    if x.is_Indexed or x.is_Sliced:
                        indices = tuple(index._subs(old, new, **kwargs) for index in x.indices)
                        if x.indices != indices:
                            x = x.func(x.base, *indices)
                    limits.append((x, *(e._subs(old, new, **kwargs) for e in ab)))
                       
                cond = self.func(function, *limits)
            else:
                cond = self._subs(old, new, **kwargs)
            return Inference(cond, given=self)
        
        assert not old.is_given
        domain = old.domain_bounded
        if domain is not None and new not in domain:
            from sympy import NotElement
            if self.is_ForAll:
                assert old not in self.variables, 'not supported in built-in axioms, please employ proved theorems: algebra.all.then.ou.subs'
                if self.expr._has(old):
                    function = self.expr._subs(old, new) | NotElement(new, domain)
                    cond = self.func(function, *limits)
                else: 
                    limits = []
                    for limit in self.limits:
                        x, *ab = limit
                        limit = (x, *[a._subs(old, new) for a in ab])
                        limits.append(limit)
                    
                    cond = self.func(self.expr, *limits) | NotElement(new, domain)
            else:
                _old = old.unbounded
                cond = self._subs(old, _old) | NotElement(_old, old.domain)
                if _old != new:
                    cond = cond._subs(_old, new, **kwargs)
        else:
            cond = self._subs(old, new, **kwargs)
            
        if self.plausible:
            return Inference(cond, given=self)
        return Inference(cond, plausible=None)
    
    def set_clause(self, clue, eqs, force=False):
        if clue == 'equivalent':
            if force:
                self.equivalent = None
            self.equivalent = eqs
        elif clue == 'given':
            if force:
                self.given = None
            self.given = eqs
        elif clue == 'imply':
            if force:
                self.imply = None
            self.imply = eqs

    @property
    def reversed(self):
        return Inference(self.cond.reversed, equivalent=self)
        
    def __and__(self, other):
        return Inference(self.cond & other.cond, equivalent=(self, other))
    
    def __add__(self, other):
        if self.is_Quantifier:
            return self.this.expr + other
        
        if isinstance(other, int):
            other = sympify(other)
        
        if self.is_Equal:
            if not other.is_Boolean and not other.is_set:
                return Inference(self.func(self.lhs + other, self.rhs + other), equivalent=self)
            if other.is_Relational:
                return Inference(other.func(self.lhs + other.lhs, self.rhs + other.rhs), equivalent=(self, other))
            
        elif self.is_Relational:
                 
            if not other.is_Boolean and not other.is_set:
                return Inference(self.func(self.lhs + other, self.rhs + other), equivalent=self)
            if other.is_Equal:
                return Inference(self.func(self.lhs + other.lhs, self.rhs + other.rhs), equivalent=(self, other))
            if self.func == other.func:
                return Inference(self.func(self.lhs + other.lhs, self.rhs + other.rhs), given=(self, other))
    
    def __rsub__(self, other):
        other = sympify(other)
        if self.is_Equal:
            assert not other.is_Relational
            return self.func(other - self.lhs, other - self.rhs, equivalent=self).simplify()
    
    def __sub__(self, other):
        if self.is_Quantifier:
            return self.this.expr - other
                
        if isinstance(other, int):
            other = sympify(other)
                    
        if self.is_Equal:
            if not other.is_Boolean and not other.is_set:
                return Inference(self.func(self.lhs - other, self.rhs - other), equivalent=self)
            if other.is_Relational:
                return Inference(other.func.reversed_type(self.lhs - other.lhs, self.rhs - other.rhs), equivalent=(self, other))
            
        elif self.is_Relational:
            if isinstance(other, int) or not other.is_Boolean and not other.is_set:
                return Inference(self.func(self.lhs - other, self.rhs - other), equivalent=self)
            if other.is_Equal:
                return Inference(self.func(self.lhs - other.lhs, self.rhs - other.rhs), equivalent=(self, other))
    
    def __pow__(self, other):
        if self.is_Equal:
            other = sympify(other)
            if other.is_positive:
                return self.func(self.lhs ** other, self.rhs ** other, given=self)
        elif self.is_Quantifier:
            return self.this.expr * other
        
    def __mod__(self, other):
        other = sympify(other)
        assert other.is_integer
        if self.is_Equal: 
            return self.func(self.lhs % other, self.rhs % other, given=self)
        elif self.is_Quantifier:
            return self.this.expr % other
            
    def __mul__(self, other):
        if self.is_Quantifier:
            return self.this.expr * other
                
        if isinstance(other, int):
            other = sympify(other)
            
        if self.is_Equal:
            if other.is_Equal:
                if other.lhs.is_nonzero or other.rhs.is_nonzero:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, equivalent=(self, other))
                return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=(self, other))
                
            elif not other.is_Boolean and not other.is_set:
                if other.is_nonzero:
                    return self.func(self.lhs * other, self.rhs * other, equivalent=self)
                return self.func(self.lhs * other, self.rhs * other, given=self)
            
        if not other.is_Boolean:
            if self.is_Relational: 
                if other > 0:
                    return Inference(self.func(self.lhs * other, self.rhs * other), equivalent=self)
                if other < 0:
                    return Inference(self.func.reversed_type(self.lhs * other, self.rhs * other), equivalent=self)
                
                if self.is_GreaterEqual or self.is_LessEqual:
                    if other >= 0:
                        return Inference(self.func(self.lhs * other, self.rhs * other), given=self)
                    if other <= 0:
                        return Inference(self.func.reversed_type(self.lhs * other, self.rhs * other), given=self)
                
        if self.is_Greater:
            if other.is_Greater:
                if self.rhs.is_extended_nonnegative: 
                    if other.rhs.is_extended_nonnegative:
                        return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=(self, other))
                if self.lhs.is_extended_nonpositive: 
                    if other.lhs.is_extended_nonpositive:
                        return self.reversed_type(self.lhs * other.lhs, self.rhs * other.rhs, given=(self, other))
        
    def __matmul__(self, rhs):
        if self.is_Quantifier:
            return self.this.expr @ rhs
        
        if rhs.is_Equal:
            if rhs.lhs.is_invertible or rhs.rhs.is_invertible:
                return self.func(self.lhs @ rhs.lhs, self.rhs @ rhs.rhs, equivalent=(self, rhs))
            return self.func(self.lhs @ rhs.lhs, self.rhs @ rhs.rhs, given=(self, rhs))

        else: 
            assert not rhs.is_bool
            if rhs.is_invertible:
                return self.func(self.lhs @ rhs, self.rhs @ rhs, equivalent=self)
            return self.func(self.lhs @ rhs, self.rhs @ rhs, given=self)
            
    def __rmatmul__(self, lhs):
        if self.is_Quantifier:
            return lhs @ self.this.expr
        
        if lhs.is_Equal:
            if lhs.lhs.is_invertible or lhs.rhs.is_invertible:
                return self.func(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs, equivalent=(lhs, self))
            return self.func(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs, given=(lhs, self))

        else: 
            assert not lhs.is_bool
            if lhs.is_invertible:
                return self.func(lhs @ self.lhs, lhs @ self.rhs, equivalent=self)
            return self.func(lhs @ self.lhs, lhs @ self.rhs, given=self)
        
    def __truediv__(self, other):
        if self.is_Quantifier:
            return self.this.expr / other
        
        if isinstance(other, int):
            other = sympify(other)
                    
        if self.is_Relational: 
            if self.is_Equal:
                if other.is_Equal:
                    assert other.lhs.is_nonzero or other.rhs.is_nonzero
                    return self.func(self.lhs / other.lhs, self.rhs / other.rhs, given=(self, other))
                    
                lhs = (self.lhs / other).ratsimp().simplify()
                rhs = (self.rhs / other).ratsimp().simplify()

                if other.is_nonzero:
                    return self.func(lhs, rhs, equivalent=self)
                from sympy import Or, Zeros
                return Or(self.func(other, Zeros(*other.shape)), self.func(lhs, rhs), equivalent=self)
                            
            if other.is_positive:
                return Inference(self.func(self.lhs / other, self.rhs / other), equivalent=self)
            if other.is_negative:
                return Inference(self.func.reversed_type(self.lhs / other, self.rhs / other), equivalent=self)
        
    def __rtruediv__(self, other):
        if isinstance(other, int):
            other = sympify(other)
                    
        if self.is_Equal:
            lhs = (other / self.lhs).ratsimp().simplify()
            rhs = (other / self.rhs).ratsimp().simplify()

            if other.is_nonzero:
                return self.func(lhs, rhs, equivalent=self)
            from sympy import Or, Zeros
            return Or(self.func(other, Zeros(*other.shape)), self.func(lhs, rhs), equivalent=self)
        
    def __iter__(self):
        raise TypeError
            
    def __getitem__(self, indices):
        if self.is_Equal: 
            if isinstance(indices, slice):
                size = self.rhs.shape[0]
                start, stop, step = indices.start, indices.stop, indices.step
                if stop is not None:
                    assert self.bound_check(stop, upper=size), "try to prove %s <= %s" % (stop, size)         
            
            return self.func(self.lhs[indices], self.rhs[indices], given=self)
        elif self.is_Quantifier:
            return self.this.expr[indices]

    def is_equivalent_of(self, rhs):
        while True:
            if self == rhs:
                return True
            equivalent = self.equivalent
            if equivalent is None:
                return False
            
            if isinstance(equivalent, (list, tuple)):
                equivalent = plausibles(equivalent)                
                if len(equivalent) != 1:
                    return False
                equivalent, *_ = equivalent
            self = equivalent

    def is_given_by(self, given):
        while True:
            equivalent = equivalent_ancestor(self)
            if len(equivalent) != 1:
                return False
            [equivalent] = equivalent
            
            if equivalent is self:
                return False
            
            if isinstance(equivalent.given, (list, tuple)):
                for i, g in enumerate(equivalent.given):
                    if g is not given:
                        continue
                    if all(g.plausible is None for j, g in enumerate(equivalent.given) if j != i):
                        return True
            elif equivalent.given is given:
                return True
            
            self = equivalent
            
    def given_by(self, given):
        if given.imply is self:
            if isinstance(self.given, tuple):
                for g in self.given:
                    if g.plausible is None:
                        continue
                    
                    if g == given.cond or g == given or g.given_by(given):
                        continue
                    
                    return
            return True

        if self.given is given or given.equivalent is self or self.equivalent is given:
            return True
        
        while True:
            equivalent = equivalent_ancestor(self)
            if len(equivalent) != 1:
                return False
            [equivalent] = equivalent
            
            if isinstance(equivalent.given, (list, tuple)):
                for g in equivalent.given:
                    if g.plausible is None or g == given or g.given_by(given):
                        ...
                    else:
                        break
                else:
                    return True
                    
                if isinstance(given.equivalent, (list, tuple)):
                    if {*equivalent.given} == {*given.equivalent}:
                        return True

            elif equivalent.given is not None:
                if equivalent.given is given:
                    return True
                if equivalent.given.given_by(given):
                    return True
            
            if equivalent is self:
                if self == given:
                    return True
                
                if given.imply is not None:
                    if isinstance(equivalent := given.imply.equivalent, tuple):
                        try:
                            index = equivalent.index(given.cond)
                            equivalent = [*equivalent]
                            del equivalent[index]
                            equivalent, = equivalent
                            return self.given_by(equivalent)
                        except:
                            ...

                    return self.given_by(given.imply)

                given = equivalent_ancestor(given)
                if len(given) != 1:
                    return False
                given, = given

                if self == given:
                    return True
                
                if given.imply is not None:
                    return self.given_by(given.imply)

                return False
            self = equivalent
            
def equivalent_ancestor(a):
    if a is None:
        return a
    while True:
        equivalent = a.equivalent
        if equivalent is None:
            return {a}

        if isinstance(equivalent, (list, tuple)):
            res = set()
            for e in equivalent:
                if e.plausible:
                    res |= equivalent_ancestor(e)
            return res

        a = equivalent

            
from sympy.core.sympify import converter, sympify

converter[Inference] = lambda infer: infer.cond

from sympy.core.assumptions import IndexedOperator
converter[IndexedOperator] = lambda op: op.basic

from sympy.core.core import Wanted
converter[Wanted] = lambda wanted: wanted

def sympify_dict(dic):
    if len(dic) == 1:
        [(key, value)] = dic.items()
        if isinstance(key, Basic):
            if key.is_Element:
                x, domain = key.args
                return conditionset(x, value, domain)
            elif key.is_symbol:
                return conditionset(key, value)
            elif value.is_Element:
                sym, base = value.args
                return imageset(sym, key, base)
 
converter[dict] = lambda dic: sympify_dict(dic)


def process_equivalent(equivalent, value):
    if value:
        if isinstance(equivalent, (list, tuple)):
            plausibility_array = plausibles(equivalent)
            if len(plausibility_array) == 1:
                plausibility_array[0].plausible = True
                return

            for eq in plausibility_array:
                eq.plausible = True
                
            return

        equivalent.plausible = True
        return
    else:
        if isinstance(equivalent, (list, tuple)):
            plausibility_array = plausibles(equivalent)
            if len(plausibility_array) == 1:
                plausibility_false = plausibles_false(equivalent)
                if not plausibility_false:
                    plausibility_array[0].plausible = False
            else:
                given = {p.given for p in plausibility_array}
                if len(given) == 1:
                    given, *_ = given
                    if given is not None:
                        given.plausible = False
                    
        else:
            equivalent.plausible = False


def process_imply(imply, value):
    if value:
        if isinstance(imply, tuple):
            for imply in imply:
                imply.plausible = True

        elif isinstance(imply.given, tuple):
#                 imply will be true unless all of imply.given is proven true!
            if all(g.plausible is None for g in imply.given):
                imply.plausible = True
            else:
                given = [g for g in imply.given if g.plausible]
                if len(given) == 1:
#                  imply will be dependent only on the single plausible theorem, so removing given links!
                    given, = given
                    imply.given = None
                    if not imply._assumptions:
                        imply._assumptions['plausible'] = True

                    assert given.imply is imply
                    if given.given is not None and isinstance(equivalent := imply.equivalent, tuple) and len(equivalent) == 2:
                        if given is equivalent[0]:
                            equivalent = equivalent[1]
                        elif given is equivalent[1]:
                            equivalent = equivalent[0]
                        else:
                            return

                        imply.equivalent = None
                        given.imply = None
                        while True:
                            given = equivalent_ancestor(given)
                            if len(given) == 1:
                                given, = given
                                if given.given is not None:
                                    given = given.given
                                else:
                                    break
                            else:
                                return

                        given.imply = equivalent

        else:
            imply.plausible = True


def process_negation(negation, value):
    plausible = negation.plausible
    if value:
        if plausible:
            negation.plausible = False
        else:
            assert plausible is False
    else:
        if plausible:
            negation.plausible = True
        else:
            assert plausible is None


def process_given(given, value):
    if value:
        if isinstance(given, (list, tuple)):
            given = plausibles(given)
            if len(given) == 2:
                set_equivalence_relationship(*given)

    else:
        if isinstance(given, (list, tuple, set)):
            given = plausibles(given)
            match len(given):
                case 1:
                    given[0].plausible = False
                case 2:
                    from sympy import Imply
                    if Imply(given[0], given[1], plausible=True).plausible is None:
                        given[1].plausible = False
                    
                    if Imply(given[1], given[0], plausible=True).plausible is None:
                        given[0].plausible = False
        else:
            given.plausible = False


def process_options(value=True, **kwargs):
    equivalent = kwargs.get('equivalent')
    if equivalent is not None:
        process_equivalent(equivalent, value)
        return

    given = kwargs.get('given')
    if given is not None:
        process_given(given, value)
        return

    imply = kwargs.get('imply')
    if imply is not None:
        process_imply(imply, value)
        return
    
    negation = kwargs.get('negation')
    if negation is not None:
        process_negation(negation, value)
        return


def plausibles(parent):
    return [eq for eq in parent if eq.plausible]


def set_equivalence_relationship(lhs, rhs):
    if lhs.set_equivalence_relationship(rhs):
        return
    if rhs.set_equivalence_relationship(lhs):
        return


def plausibles_false(parent):
    return [eq for eq in parent if eq.plausible is False]

