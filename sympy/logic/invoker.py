from types import MethodType  # , FunctionType


class Invoker:

    def __new__(cls, expr):
        this = object.__new__(cls)
        this._objs = []
        this._args = []
        this.index = []
        this._context = []
        this.append(expr)
        this.callable = None
        this._domain_defined = {}      
        return this
    
    @property
    def target(self):
        return self._objs[-1]
    
    @property
    def parent(self):
        if len(self._objs) > 1:
            return self._objs[-2]
    
    @property
    def source(self):
        return self._objs[0]

    def inference_status(self, boolean):
        for i in range(len(self.index)):
            boolean ^= self._objs[i].inference_status(self.index[i])
            
        return 'imply' if boolean else 'given'
        
    def determine_assumptions(self, obj):
        if obj.is_Inference and obj.is_Boolean: 
            equivalent = obj.equivalent
            if equivalent is not None:
                if isinstance(equivalent, (list, tuple)):
                    clue = equivalent[0].clue
                    if clue == 'given':
                        return self.inference_status(False)
                    elif clue == 'imply':
                        return self.inference_status(True)
                else:
                    # in case of result of simplify
                    if equivalent is not self.target:
                        clue = equivalent.clue
                        if clue is not None:
                            if clue == 'given':
                                return self.inference_status(False)
                            if clue == 'imply':
                                return self.inference_status(True)
                            return clue
            elif obj.given is not None: 
                return self.inference_status(False) 
            elif obj.imply is not None:
                return self.inference_status(True)
        return 'equivalent'
        
    def process_index(self, i, obj):
        this = self._objs[i - 1]
        args = [*this.args]

        index = self.index[i]
        if isinstance(index, slice):
            assert this.is_And or this.is_Or or this.is_Mul or this.is_Add or this.is_MatMul
            start, stop, step = index.start, index.stop, index.step
            if start is None:
                start = 0
            elif start < 0:
                start += len(args)

            if stop is None:
                stop = len(args)
            elif stop < 0:
                stop += len(args)
                
            if step is None:
                step = 1
                
            if step > 0:
                index, *indices = range(start, stop, step)
                indices.reverse()
            else:
                *indices, index = range(start, stop, step)
                
            for j in indices:
                del args[j]

        kwargs = this.kwargs
        try:
            args[index] = obj
        except TypeError:
            if index == 'shape':
                obj = tuple(obj)
            kwargs[index] = obj
            args = ()
        return this, args, kwargs
    
    def result(self, obj, simplify=-1, evaluate=None):
        assumptions = {self.determine_assumptions(obj): self.source}
        from sympy.core.sympify import _sympify
        obj = _sympify(obj)
        for i in range(-1, -len(self.index) - 1, -1):
            this, args, kwargs = self.process_index(i, obj)
            
            if stop := i == -len(self.index):
                kwargs = assumptions
                
            if evaluate is not None:
                kwargs['evaluate'] = evaluate
            
            if self._domain_defined and this.func.is_ExprWithLimits:
                _, *limits = args
                for i, limit in enumerate(limits):
                    if limit[0] in self._domain_defined:
                        x, domain, *dir = limit.coerce_setlimit()
                        if dir:
                            continue
                        domain_defined = self._domain_defined.pop(x)
                        if domain != domain_defined:
                            if domain_defined in domain: 
                                args[i + 1] = (x, domain_defined)
                                break
                else:
                    if this.is_ForAll:
                        for x in set(self._domain_defined):
                            if this._has(x): 
                                args.append((x, self._domain_defined.pop(x)))                    
            
            obj = this.func(*args, **kwargs)
            if simplify:
                # exclude case Exists[C](All[x](f(x) == C))
                if not obj.is_ForAll or stop or not self._objs[i - 2].is_Exists:
                    obj = obj.simplify()
                simplify -= 1
                
            if stop:
                break
        else:
            assert not len(self.index)
            obj = obj.copy(**assumptions)
             
        if obj.equivalent == self.source and obj == self.source:
            return self.source
        from sympy import Boolean
        if isinstance(self.source, Boolean):
            if 'given' in assumptions:
                from sympy import Imply
                return Imply(self.source, obj, plausible=None)
            if 'equivalent' in assumptions:
                from sympy import Iff
                return Iff(self.source, obj, plausible=None)
            if 'imply' in assumptions:
                from sympy import Given
                return Given(self.source, obj, plausible=None)
            
        return obj

    @property
    def this(self):
        return self.callable.__self__
        
    # simplify = True by default, use simplify = False in invoke, use simplify = None in simplification process after invoking!
    def __call__(self, *args, **kwargs):
        if self.callable is None:
            return self.enter(*args, **kwargs)
        
        this = self.this
        
        if any(obj.is_Exists for obj in self._objs):
            kwargs['local'] = True

        evaluate = kwargs.pop('evaluate', None)
        obj = self.invoke(*args, **kwargs)
        
        if self.callable.__name__ == 'subs':
            if not this.is_Quantifier:
                assert all(arg.is_Equal for arg in args)
                assert all(arg.plausible is None for arg in args)                
            self.watch_domain_defined(obj)
        else:
            for i in range(-2, -len(self._objs), -1):
                parent = self._objs[i]
                if parent.is_ExprWithLimits and not (parent.is_Expectation or parent.is_Variance or parent.is_Stack):
                    self.watch_domain_defined(obj, *parent.limits)
                    
        simplify = kwargs.get('simplify', True)
        if simplify is None:
            simplify = 0
        elif isinstance(simplify, bool):
            simplify = -1
        else:
            # warning: isinstance(True, int) or isinstance(False, int) is always True
            if simplify:
                simplify -= 1

        return self.result(obj, simplify=simplify, evaluate=evaluate)

    def invoke(self, *args, **kwargs):
        if self._context:
            this = self.this
            reps = []
            outer_context = {}
            for expr, limits in self._context:
                for x, *ab in limits:
                    if x.shape or not ab:
                        continue
                    
                    if len(ab) == 1:
                        domain, = ab
                        if domain.is_Boolean:
                            if expr.is_ExprCondPair and domain is expr.cond:
                                assert this is not domain, 'could not operate on the cond field of a piecewise expression under the condition of itself!'
                            domain = x.domain_conditioned(domain)
                        elif domain.is_ConditionSet:
                            domain = domain.base_set
                    elif len(ab) == 2 and not ab[1].is_set:
                        for i, t in enumerate(ab):
                            for outer_var in outer_context:
                                if t._has(outer_var):
                                    t = t._subs(outer_var, outer_context[outer_var][0])
                            ab[i] = t
                                
                        domain = x.range(*ab)
                        
                    if x in outer_context:
                        x, _domain = outer_context[x]
                        keys = domain.free_symbols & outer_context.keys()
                        if keys:
                            for key in keys:
                                domain = domain._subs(key, outer_context[key][0])
                        domain &= _domain
                            
                    _x = x.copy(domain=domain)
                    if x != _x:
                        this = this._subs(x, _x)
                        if this.is_ExprWithLimits and len(this.limits) > 1 and kwargs.get('simplify') is False:
                            ...
                        else:
                            this = this.simplify()

                        reps.append((x, _x))
                        outer_context[x] = (_x, domain)
            
            obj = getattr(this, self.callable.__name__)(*args, **kwargs)
            if obj.is_BooleanAtom:
                return obj
            
            reps.reverse()
            for x, _x in reps:
                _obj = obj._subs(_x, x)
                if obj.is_bool:
                    if _obj.is_BooleanAtom:
                        _obj = _obj.copy(equivalent=obj)
                obj = _obj
        else: 
            if self.callable.__func__.__code__.co_name == 'apply':
                axiom = args[0]
                __kwdefaults__ = axiom.apply.__closure__[0].cell_contents.__kwdefaults__
                if __kwdefaults__:
                    if 'assumptions' in __kwdefaults__:
                        assumptions = {}
                        for obj in self._objs:
                            if obj.is_ExprWithLimits:
                                if obj.is_Exists:
                                    for x in obj.variables:
                                        assumptions[x] = False
                                else:
                                    for x, *ab in obj.limits:
                                        assumptions[x] = ab
                        kwargs['assumptions'] = assumptions
                    elif 'simplify' in __kwdefaults__:
                        simplify = __kwdefaults__['simplify']
                        if not kwargs and not simplify:
                            kwargs['simplify'] = simplify
                
            obj = self.callable(*args, **kwargs)
        return obj
        
    def append(self, obj):
        self._objs.append(obj)

    def fetch_from_path(self, *path, struct=None):
        target = self.target
        if struct is not None: 
            _path = target.fetch_from_path(*path, struct=struct)
            if isinstance(_path, tuple):
                path += _path
            
        for index in path:
            self.index.append(index)
            target = target.args[index]
            self.append(target)
            
        return self
        
    def target_from_path(self, target, *path, struct=None):
        for index in path:
            target = target.args[index]
        return target
    
    def find(self, *query): 
        from sympy import Basic
        query, struct = Basic.make_query(*query)
        
        return self.target.yield_one([(q, []) for q in query],
                                   foreach=Basic.find_path,
                                   func=self.target_from_path,
                                   fetch=self.fetch_from_path,
                                   output=[],
                                   struct=struct)
                                    
    method2index = {'rhs': 1,
                    'lhs': 0,
                    'arg': 0,
                    'cond': 1,
                    'expr': 0,
                    'base': 0}

    def watch_domain_defined(self, obj, *limits):
        # beware that application of definition may cause the domain definition to be altered, thus causing logic error!
        target = self.target
        if not limits:
            from sympy import Tuple
            limits = [Tuple(v) for v in target.free_symbols]

        for limit in limits:
            x, *ab = limit
            original_domain = target.domain_defined(x)
            altered_domain = obj.domain_defined(x)
            if original_domain != altered_domain:
                if original_domain in altered_domain:
                    ...
                else:
                    x, domain = limit.coerce_setlimit()
                    assert original_domain & domain in altered_domain & domain, "original domain of definition must lie in transformed domain of definition!"                    
                assert x not in self._domain_defined
                self._domain_defined[x] = original_domain
        
    def __getattr__(self, method): 
        target = self.target
        if method == 'T':
            if len(target.shape) > 1:
                return self
            
        obj = getattr(target, method)
        
        if method == 'definition':
            self.watch_domain_defined(obj)
            return self.result(obj)
            
        if isinstance(obj, MethodType):
            self.callable = obj
            return self

        if isinstance(obj, tuple):
            self.append(obj)
            return self
        
        index = self.method2index.get(method)
        if index is None:
            return self.result(obj)
            
        if obj is not target.args[index]:
            assert method in ('lhs', 'rhs')
            self.index.append(0)
            self.append(target.args[0])
        
        self.index.append(index)
        self.append(obj)

        return self

    def __neg__(self):
        if self.target.is_Relational:
            self.callable = self.target.__neg__
            return self.__call__()

    def __sub__(self, rhs):
        if self.target.is_Relational:
            self.callable = self.target.__sub__
            return self.__call__(rhs)
        
    def __add__(self, rhs):
        if self.target.is_Relational:
            self.callable = self.target.__add__
            return self.__call__(rhs)
        
    def __truediv__(self, rhs):
        if self.target.is_Relational:
            self.callable = self.target.__truediv__
            return self.__call__(rhs)

    def __mul__(self, rhs):
        if self.target.is_Relational:
            self.callable = self.target.__mul__
            return self.__call__(rhs)

    def __mod__(self, rhs):
        if self.target.is_Equal:
            self.callable = self.target.__mod__
            return self.__call__(rhs)
        
    def __matmul__(self, rhs):
        if self.target.is_Equal:
            self.callable = self.target.__matmul__
            return self.__call__(rhs)

    def __str__(self):
        return str(self.target)

    def __len__(self):
        return len(self.target)

    __repr__ = __str__
    
    @property
    def latex(self):
        target = self.target
        try:
            return target.latex
        except AttributeError:
            if isinstance(target, tuple):
                return r"\left[\begin{array}{%s}%s\end{array}\right]" % ('c', r'\\'.join(t.latex for t in target))
        except Exception as e:
            raise

    def _pretty(self, p):
        return p._print(self.target)

    def __getitem__(self, indices):
        target = self.target
        
        if isinstance(target, tuple):
            obj = target[indices]
             
            parent = self.parent
            if isinstance(indices, slice):
                assert parent.is_And or parent.is_Or or parent.is_Mul or parent.is_Add or parent.is_MatMul and isinstance(indices, slice) and (indices.step is None or indices.step == 1)
                index = indices
                obj = parent.func(*obj)
            else:
                try:
                    index = parent.args.index(obj)
                except ValueError:
                    for key, value in parent.kwargs.items():
                        if key == 'shape':
                            try:
                                index = value.index(obj)
                                self.index.append('shape')
                                from sympy import Tuple
                                self._objs[-1] = Tuple(*target)
                                self._objs.append(obj)
                                break
                            except ValueError:
                                continue
                        elif obj == value:
                            index = key
                            break
                
            self.index.append(index)
            self._objs[-1] = obj
        elif target.is_Tuple:
            self.index.append(indices)
            self._objs.append(target[indices])
        elif target.is_Matrix:
            if isinstance(indices, tuple):
                i, j = indices
                index = i * target.cols + j
            else:
                index = indices
            
            self.index.append(index)
            self._objs.append(target.args[index])
        else:
            self = self.result(target[indices]) 
                        
        return self

    def __iter__(self):
        return iter(self.obj)

    def enter(self, *args, **kwargs):
        target = self.target
        limits = target.limits_in_context(args or kwargs, self.parent)

        if args:
            for x in args:
                if target.is_ExprWithLimits and x in target.variables:
                    if target.is_Stack:
                        continue
                    else:
                        expr = target.expr
                else:
                    expr = target
                    
                limits.append((x, expr.domain_defined(x)))
                            
        if kwargs: 
            if 'shape' in kwargs:
                shape = kwargs['shape']
                limits = tuple(limit for limit in limits if limit[0].shape == shape)
            elif 'var' in kwargs:
                var = kwargs['var']
                limits = tuple(limit for limit in limits if limit[0] == var)                
                          
        self._context.append((target, limits))
        return self

    def __or__(self, x):
        if self.assumptions is None:
            self.assumptions = []
        target = self.target
        domain = target.domain_defined(x)
        self.assumptions.append((x, domain))
        return self


class Identity(Invoker):

    def result(self, obj, simplify=True): 
        from sympy import Equal
        
        for i in range(-1, -len(self.index) - 1, -1):
            this, args, kwargs = self.process_index(i, obj)

            obj = this.func(*args, **kwargs)
            if simplify:
                obj = obj.simplify()

        return Equal(self.source, obj, evaluate=False, plausible=None)            
        
    def __call__(self, *args, **kwargs):
        if self.callable is None:
            return self.enter(*args)
        
        if self.callable.__name__ == 'subs':
            this = self.this
            if this.is_AddWithLimits:
                if len(args) == 2:
                    (x, *_), *_ = this.limits
                    # domain might be different!
                    assert args[0].name == x.name
            else: 
                assert all(arg.is_Equal and arg.plausible is None for arg in args)                
                args = map(lambda inf: inf.cond, args)

        obj = self.invoke(*args, **kwargs)
        
        return self.result(obj, simplify=kwargs.get('simplify', True) is not None)

