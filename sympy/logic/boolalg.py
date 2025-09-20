"""
Boolean algebra module for SymPy
"""
import re
from collections import defaultdict
from itertools import combinations, product
from sympy.core.add import Add
from sympy.core.basic import Basic
from sympy.core.cache import cacheit
from sympy.core.compatibility import ordered, with_metaclass, as_int
from sympy.core.function import Application, Derivative
from sympy.core.numbers import Number
from sympy.core.operations import LatticeOp
from sympy.core.singleton import Singleton, S
from sympy.core.sympify import converter, _sympify, sympify
from sympy.utilities.iterables import sift, ibin
from sympy.utilities.misc import filldedent
from sympy.logic.invoker import Invoker


def as_Boolean(e):
    """Like bool, return the Boolean value of an expression, e,
    which can be any instance of Boolean or bool.

    Examples
    ========

    >>> from sympy import true, false, nan
    >>> from sympy.logic.boolalg import as_Boolean
    >>> from sympy.abc import x
    >>> as_Boolean(0) is false
    True
    >>> as_Boolean(1) is true
    True
    >>> as_Boolean(x)
    x
    >>> as_Boolean(2)
    Traceback (most recent call last):
    ...
    TypeError: expecting bool or Boolean, not `2`.
    >>> as_Boolean(nan)
    Traceback (most recent call last):
    ...
    TypeError: expecting bool or Boolean, not `nan`.

    """
    from sympy.core.symbol import Symbol
    if e == True:
        return S.true
    if e == False:
        return S.false
    if isinstance(e, Symbol):
        z = e.is_zero
        if z is None:
            return e
        return S.false if z else S.true
    if isinstance(e, Boolean):
        return e
    raise TypeError('expecting bool or Boolean, not `%s`.' % e)


class Boolean(Basic):
    """A boolean object is an object for which logic operations make sense."""

    is_bool = True
    plausible = None
    __slots__ = ()

    def simplify_condition_on_random_variable(self):
        return self
        
    def sanctity_check(self, *limits):
        from sympy.concrete.expr_with_limits import limits_dict
        for x, domain in limits_dict(limits).items():
            if isinstance(domain, list):
                continue
            if domain not in self.domain_defined(x):
                return False
        return True
        
    def simplify(self, deep=False, wrt=None, **kwargs):
        if wrt is not None:
            domain_defined = self.domain_defined(wrt)
            if domain_defined != wrt.domain:
                _wrt = wrt.copy(domain=domain_defined, **wrt._assumptions)
                this = self._subs(wrt, _wrt).simplify(deep=True)._subs(_wrt, wrt)
                if this != self: 
                    this.equivalent = self
                    return this
            return self
        
        if deep:
            hit = False
            args = []
            for arg in self.args: 
                _arg = arg.simplify(deep=deep)
                
                if _arg != arg:
                    hit = True
                args.append(_arg)
            if hit:
                return self.func(*args).simplify()
        return self

    def apply(self, axiom, *args, **kwargs):
        eqs = axiom.apply(self, *args, **kwargs)
        if isinstance(eqs, (list, tuple)):
            eqs = And(*eqs, equivalent=eqs)
        elif eqs.is_Equivalent:
            if eqs.clue is None:
                if self is eqs.lhs:
                    return eqs.rhs
        return eqs

    def existent_symbols(self):
        from sympy.tensor.indexed import Indexed, Sliced
        from sympy.stats.rv import RandomSymbol
        free_symbols = {*self.free_symbols}        
        for symbol in self.free_symbols:
            if symbol.is_given or symbol.is_bool:
                free_symbols.discard(symbol)
                continue
                        
            if isinstance(symbol, (RandomSymbol, Indexed, Sliced)):
                free_symbols -= symbol.free_symbols
                free_symbols.add(symbol)

        deletes = set()
        for y in free_symbols:
            deletes |= y.domain.free_symbols
            
        free_symbols -= deletes
        return free_symbols

    def limits_exists(self):
        return [(s,) for s in self.existent_symbols()]
        
    def __invert__(self):
        """Return the negated relationship.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> Eq(x, 1)
        Eq(x, 1)
        >>> ~_
        Ne(x, 1)
        >>> x < 1
        x < 1
        >>> ~_
        x >= 1

        Notes
        =====

        This works more or less identical to ``~``/``Not``. The difference is
        that ``negated`` returns the relationship even if `evaluate=False`.
        Hence, this is useful in code when checking for e.g. negated relations
        to exisiting ones as it will not be affected by the `evaluate` flag.
        """
        invert = self.invert()
        limits_exists = self.limits_exists()
        invert |= self.domain_definition().invert()
        
        if limits_exists:
            from sympy import Any
            return Any(invert, *limits_exists, negation=self).simplify()
        
        return invert.copy(negation=self)        

    def invert(self):
        return Boolean.__new__(self.invert_type, *self.args)

    def __new__(cls, *args, **kwargs):
        for name, value in [*kwargs.items()]:
            if value is None:
                del kwargs[name]
        return Basic.__new__(cls, *args, **kwargs)

    @property
    def this(self):
        return Invoker(self)

    def __rshift__(self, other):
        """Overloading for >>"""
        return Imply(self, other)

    def __lshift__(self, other):
        """Overloading for <<"""
        return Given(self, other)

    __rrshift__ = __lshift__
    __rlshift__ = __rshift__

    def __xor__(self, other):
        return Xor(self, other)

    __rxor__ = __xor__

    def equals(self, other):
        """
        Returns True if the given formulas have the same truth table.
        For two formulas to be equal they must have the same literals.

        Examples
        ========

        >>> from sympy.abc import A, B, C
        >>> from sympy.logic.boolalg import And, Or, Not
        >>> (A >> B).equals(~B >> ~A)
        True
        >>> Not(And(A, B, C)).equals(And(Not(A), Not(B), Not(C)))
        False
        >>> Not(And(A, Not(A))).equals(Or(B, Not(B)))
        False
        """
        from sympy.logic.inference import satisfiable
        from sympy.core.relational import Relational

        if self.has(Relational) or other.has(Relational):
            raise NotImplementedError('handling of relationals')
        return self.atoms() == other.atoms() and \
            not satisfiable(Not(Equivalent(self, other)))

    def to_nnf(self, simplify=True):
        # override where necessary
        return self

    def as_set(self):
        """
        Rewrites Boolean expression in terms of real sets.

        Examples
        ========

        >>> from sympy import Symbol, Eq, Or, And
        >>> x = Symbol('x', real=True)
        >>> Eq(x, 0).as_set()
        {0}
        >>> (x > 0).as_set()
        Interval.open(0, oo)
        >>> And(-2 < x, x < 2).as_set()
        Interval.open(-2, 2)
        >>> Or(x < -2, 2 < x).as_set()
        Union(Interval.open(-oo, -2), Interval.open(2, oo))
        """
        from sympy.calculus.util import periodicity
        from sympy.core.relational import Relational
        free = self.free_symbols
        if len(free) == 1:
            x, = free
            reps = {}
            for r in self.atoms(Relational):
                if periodicity(r, x) not in (0, None):
                    s = r._eval_as_set()
                    if s.is_EmptySet or s.is_UniversalSet or s == Reals:
                        reps[r] = s.as_relational(x)
                        continue
                    raise NotImplementedError(filldedent('''
                        as_set is not implemented for relationals
                        with periodic solutions
                        '''))
            return self.subs(reps)._eval_as_set()
        else:
            raise NotImplementedError("Sorry, as_set has not yet been"
                                      " implemented for multivariate"
                                      " expressions")

    @property
    def binary_symbols(self):
        from sympy.core.relational import Eq, Ne
        return set().union(*[i.binary_symbols for i in self.args if i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne))])

    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        return dtype.bool

    def _eval_shape(self): 
        return ()

    def overwrite(self, origin, **assumptions):
        if origin != self:
            for k, v in assumptions.items():
                self._assumptions[k] = v
            return self
        return origin

    def _eval_is_random(self):
        for arg in self.args:
            if arg.is_random:
                return True

    @property
    def wrt(self):
        return next(iter(self.free_symbols))

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

    def domain_conditioned(self, x):
        if self._has(x):
            from sympy.sets import conditionset
            return conditionset(x, self, x.domain)
        return x.domain
        from sympy.functions.elementary.piecewise import Piecewise
        return Piecewise((x.domain, self), (x.emptySet, True))

    @classmethod
    def unnest(cls, expr, limits, symbols, evaluate=True, **assumptions):
    # unnest any nested calls
        if evaluate:
            while cls == type(expr):
                limits = list(expr.limits) + limits
                expr = expr.expr

        if not limits and symbols:
            return expr.copy(**assumptions)

        return Boolean.__new__(cls, expr, *limits, **assumptions)


class BinaryCondition(Boolean):
    """Base class for all binary relation types.
    """
    __slots__ = ()
    
    @property
    def lhs(self):
        """The left-hand side of the relation."""
        return self._args[0]

    @property
    def rhs(self):
        """The right-hand side of the relation."""
        return self._args[1]

    @property
    def reversed(self):
        """Return the relationship with sides reversed.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> Eq(x, 1)
        Eq(x, 1)
        >>> _.reversed
        Eq(1, x)
        >>> x < 1
        x < 1
        >>> _.reversed
        1 > x
        """
        a, b = self.args
        return self.reversed_type(b, a, evaluate=False)

    @cacheit
    def _eval_domain_defined(self, x, **_):
        return self.lhs.domain_defined(x) & self.rhs.domain_defined(x)

    def domain_definition(self, **_):
        return self.lhs.domain_definition() & self.rhs.domain_definition()
    
    def __bool__(self):
        return False
    
    @staticmethod
    def eval(cls, *args, **options):
        if options.pop('sympify', True):
            args = tuple(map(sympify, args))
        from sympy.core.parameters import global_parameters
        if options.pop('evaluate', global_parameters.evaluate):
            evaluated = cls.eval(*args)
            if evaluated is not None:

                if options and evaluated.is_BooleanAtom and 'plausible' in options:
                    if evaluated:
                        options['plausible'] = None
                    else:
                        options['plausible'] = False
                else:
                    return evaluated.copy(**options)
                
        if options:
            from sympy.core.inference import Inference
            return Inference(BinaryCondition.__new__(cls, *args), **options)            
                
        return BinaryCondition.__new__(cls, *args, **options)
    
    @property
    def wrt(self):
        free_symbols = self.lhs.free_symbols
        if not free_symbols:
            free_symbols = self.rhs.free_symbols
        return next(iter(free_symbols))
    
    def subs(self, *args, **kwargs):
        if all(isinstance(arg, Boolean) for arg in args):
            res = self
            for eq in args:
                res = res.subs(eq)
            return res
        
        old, new = args
        if old.is_Sliced:
            return self._subs_sliced(old, new)
        if not old.is_symbol:
            return self
        
        new = sympify(new)
        domain = old.domain_bounded
        if domain is not None and new not in domain:
            return self

        return self.func(self.lhs._subs(*args, **kwargs).simplify(), self.rhs._subs(*args, **kwargs).simplify())

    @property
    def variables(self):
        return {*self.lhs.variables} | {*self.rhs.variables}

    @cacheit
    def sort_key(self, order=None):
        args = self.args
        args = len(args), tuple(arg.class_key() for arg in args), tuple(arg.sort_key(order=order) for arg in args)
        
        exp = S.One
        exp = exp.sort_key(order=order)

        return self.class_key(), args, exp, 1


class BooleanAssumption(BinaryCondition):
    ...
        

class BooleanAtom(Boolean):
    """
    Base class of BooleanTrue and BooleanFalse.
    """
#     is_Boolean = True
    is_Atom = True
    _op_priority = 11  # higher than Expr
    
    def simplify(self, *a, **kwargs):
        return self

    def expand(self, *a, **kw):
        return self

    @property
    def canonical(self):
        return self

    def _noop(self, other=None):
        raise TypeError('BooleanAtom not allowed in this context.')

    __add__ = _noop
    __radd__ = _noop
    __sub__ = _noop
    __rsub__ = _noop
    __mul__ = _noop
    __rmul__ = _noop
    __pow__ = _noop
    __rpow__ = _noop
    __rdiv__ = _noop
    __truediv__ = _noop
    __div__ = _noop
    __rtruediv__ = _noop
    __mod__ = _noop
    __rmod__ = _noop
    _eval_power = _noop

    # /// drop when Py2 is no longer supported
    def __lt__(self, other):
        from sympy.utilities.misc import filldedent
        raise TypeError(filldedent('''
            A Boolean argument can only be used in
            Eq and Ne; all other relationals expect
            real expressions.
        '''))

    __le__ = __lt__
    __gt__ = __lt__
    __ge__ = __lt__

    def _pretty(self, p):
        return p._print(self.func.__name__)


class BooleanTrue(with_metaclass(Singleton, BooleanAtom)):
    """
    SymPy version of True, a singleton that can be accessed via S.true.

    This is the SymPy version of True, for use in the logic module. The
    primary advantage of using true instead of True is that shorthand boolean
    operations like ~ and >> will work as expected on this class, whereas with
    True they act bitwise on 1. Functions in the logic module will return this
    class when they evaluate to true.

    Notes
    =====

    There is liable to be some confusion as to when ``True`` should
    be used and when ``S.true`` should be used in various contexts
    throughout SymPy. An important thing to remember is that
    ``sympify(True)`` returns ``S.true``. This means that for the most
    part, you can just use ``True`` and it will automatically be converted
    to ``S.true`` when necessary, similar to how you can generally use 1
    instead of ``S.One``.

    The rule of thumb is:

    "If the boolean in question can be replaced by an arbitrary symbolic
    ``Boolean``, like ``Or(x, y)`` or ``x > 1``, use ``S.true``.
    Otherwise, use ``True``"

    In other words, use ``S.true`` only on those contexts where the
    boolean is being used as a symbolic representation of truth.
    For example, if the object ends up in the ``.args`` of any expression,
    then it must necessarily be ``S.true`` instead of ``True``, as
    elements of ``.args`` must be ``Basic``. On the other hand,
    ``==`` is not a symbolic operation in SymPy, since it always returns
    ``True`` or ``False``, and does so in terms of structural equality
    rather than mathematical, so it should return ``True``. The assumptions
    system should use ``True`` and ``False``. Aside from not satisfying
    the above rule of thumb, the assumptions system uses a three-valued logic
    (``True``, ``False``, ``None``), whereas ``S.true`` and ``S.false``
    represent a two-valued logic. When in doubt, use ``True``.

    "``S.true == True is True``."

    While "``S.true is True``" is ``False``, "``S.true == True``"
    is ``True``, so if there is any doubt over whether a function or
    expression will return ``S.true`` or ``True``, just use ``==``
    instead of ``is`` to do the comparison, and it will work in either
    case.  Finally, for boolean flags, it's better to just use ``if x``
    instead of ``if x is True``. To quote PEP 8:

    Don't compare boolean values to ``True`` or ``False``
    using ``==``.

    * Yes:   ``if greeting:``
    * No:    ``if greeting == True:``
    * Worse: ``if greeting is True:``

    Examples
    ========

    >>> from sympy import sympify, true, false, Or
    >>> sympify(True)
    True
    >>> _ is True, _ is true
    (False, True)

    >>> Or(true, false)
    True
    >>> _ is true
    True

    Python operators give a boolean result for true but a
    bitwise result for True

    >>> ~true, ~True
    (False, -2)
    >>> true >> true, True >> True
    (True, 0)

    Python operators give a boolean result for true but a
    bitwise result for True

    >>> ~true, ~True
    (False, -2)
    >>> true >> true, True >> True
    (True, 0)

    See Also
    ========
    sympy.logic.boolalg.BooleanFalse

    """

    def __bool__(self):
        return True

    def __hash__(self):
        return hash(True)

    def invert(self):
        return S.false

    def as_set(self):
        """
        Rewrite logic operators and relationals in terms of real sets.

        Examples
        ========

        >>> from sympy import true
        >>> true.as_set()
        UniversalSet
        """
        from sympy.sets.sets import UniversalSet
        return UniversalSet()

    def copy(self, **kwargs):
        if kwargs:
            from sympy.core.inference import Inference
            return Inference(self, **kwargs)
        return self

    def overwrite(self, _, **assumptions):
        return self.copy(**assumptions)        

    def domain_conditioned(self, x):
        return x.domain

    def _pretty(self, p): 
        return p._print('True')

    @property
    def numpy(self):
        import numpy as np
        return np.array(True)
    
    def _sympystr(self, p):
        return "True"

    def _lean(self, p):
        return "True"
    
    def _latex(self, p):
        return r"\text{True}"


class BooleanFalse(with_metaclass(Singleton, BooleanAtom)):
    """
    SymPy version of False, a singleton that can be accessed via S.false.

    This is the SymPy version of False, for use in the logic module. The
    primary advantage of using false instead of False is that shorthand boolean
    operations like ~ and >> will work as expected on this class, whereas with
    False they act bitwise on 0. Functions in the logic module will return this
    class when they evaluate to false.

    Notes
    ======
    See note in :py:class`sympy.logic.boolalg.BooleanTrue`

    Examples
    ========

    >>> from sympy import sympify, true, false, Or
    >>> sympify(False)
    False
    >>> _ is False, _ is false
    (False, True)

    >>> Or(true, false)
    True
    >>> _ is true
    True

    Python operators give a boolean result for false but a
    bitwise result for False

    >>> ~false, ~False
    (True, -1)
    >>> false >> false, False >> False
    (True, 0)

    See Also
    ========
    sympy.logic.boolalg.BooleanTrue

    """

    def __bool__(self):
        return False

    def __hash__(self):
        return hash(False)

    def invert(self):
        return S.true

    def as_set(self):
        """
        Rewrite logic operators and relationals in terms of real sets.

        Examples
        ========

        >>> from sympy import false
        >>> false.as_set()
        EmptySet()
        """
        from sympy import EmptySet
        return EmptySet()

    def copy(self, **kwargs):
        if kwargs:
            from sympy.core.inference import Inference
            return Inference(self, **kwargs)
        return self

    def overwrite(self, _, **assumptions):
        return self.copy(**assumptions)        

    def domain_conditioned(self, x):
        return x.emptySet

    @property
    def numpy(self):
        import numpy as np
        return np.array(False)
    
    def _sympystr(self, p):
        return "False"

    def _lean(self, p):
        return "False"
    
    def _latex(self, p):
        return r"\text{False}"


true = BooleanTrue()
false = BooleanFalse()
# We want S.true and S.false to work, rather than S.BooleanTrue and
# S.BooleanFalse, but making the class and instance names the same causes some
# major issues (like the inability to import the class directly from this
# file).
S.true = true
S.false = false

converter[bool] = lambda x: S.true if x else S.false


class BooleanFunction(Application, Boolean):
    """Boolean function is a function that lives in a boolean space
    It is used as base class for And, Or, Not, etc.
    """

    def __bool__(self):
        return False

    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        return dtype.bool

    def _eval_simplify(self, ratio, measure, rational, inverse):
        rv = self.func(*[a._eval_simplify(ratio=ratio, measure=measure,
                                          rational=rational, inverse=inverse)
                         for a in self.args])
        return simplify_logic(rv)

    # /// drop when Py2 is no longer supported
    def __lt__(self, other):
        from sympy.utilities.misc import filldedent
        raise TypeError(filldedent('''
            A Boolean argument can only be used in
            Eq and Ne; all other relationals expect
            real expressions.
        '''))

    __le__ = __lt__
    __ge__ = __lt__
    __gt__ = __lt__

    # \\\

    @classmethod
    def binary_check_and_simplify(self, *args):
        from sympy.core.relational import Relational, Eq, Ne
        args = [as_Boolean(i) for i in args]
        binary_symbols = set().union(*[i.binary_symbols for i in args])
        rel = set().union(*[i.atoms(Relational) for i in args])
        reps = {}
        for x in binary_symbols:
            for r in rel:
                if x in binary_symbols and x in r.free_symbols:
                    if isinstance(r, (Eq, Ne)):
                        if not (
                                S.true in r.args or
                                S.false in r.args):
                            reps[r] = S.false
                    else:
                        raise TypeError(filldedent('''
                            Incompatible use of binary symbol `%s` as a
                            real variable in `%s`
                            ''' % (x, r)))
        for index, i in enumerate(args):
            for x, y in reps.items():
                i = i._subs(x, y)
            args[index] = i
        return args
#         return [i.subs(reps) for i in args]

    def to_nnf(self, simplify=True):
        return self._to_nnf(*self.args, simplify=simplify)

    @classmethod
    def _to_nnf(cls, *args, **kwargs):
        simplify = kwargs.get('simplify', True)
        argset = set([])
        for arg in args:
            if not is_literal(arg):
                arg = arg.to_nnf(simplify)
            if simplify:
                if isinstance(arg, cls):
                    arg = arg.args
                else:
                    arg = (arg,)
                for a in arg:
                    if Not(a) in argset:
                        return cls.zero
                    argset.add(a)
            else:
                argset.add(arg)
        return cls(*argset)

    # the diff method below is copied from Expr class
    def diff(self, *symbols, **assumptions):
        assumptions.setdefault("evaluate", True)
        return Derivative(self, *symbols, **assumptions)

    def _eval_derivative(self, x):
        from sympy.core.relational import Eq
        from sympy.functions.elementary.piecewise import Piecewise
        if x in self.binary_symbols:
            return Piecewise(
                (0, Eq(self.subs(x, 0), self.subs(x, 1))),
                (1, True))
        elif x in self.free_symbols:
            # not implemented, see https://www.encyclopediaofmath.org/
            # index.php/Boolean_differential_calculus
            pass
        else:
            return S.Zero

    def _apply_patternbased_simplification(self, rv, patterns, measure,
                                           dominatingvalue,
                                           replacementvalue=None):
        """
        Replace patterns of Relational

        Parameters
        ==========

        rv : Expr
            Boolean expression

        patterns : tuple
            Tuple of tuples, with (pattern to simplify, simplified pattern)

        measure : function
            Simplification measure

        dominatingvalue : boolean or None
            The dominating value for the function of consideration.
            For example, for And S.false is dominating. As soon as one
            expression is S.false in And, the whole expression is S.false.

        replacementvalue : boolean or None, optional
            The resulting value for the whole expression if one argument
            evaluates to dominatingvalue.
            For example, for Nand S.false is dominating, but in this case
            the resulting value is S.true. Default is None. If replacementvalue
            is None and dominatingvalue is not None,
            replacementvalue = dominatingvalue
        """
        from sympy.core.relational import Relational, _canonical
        if replacementvalue is None and dominatingvalue is not None:
            replacementvalue = dominatingvalue
        # Use replacement patterns for Relationals
        changed = True
        Rel, nonRel = sift(rv.args, lambda i: isinstance(i, Relational),
                           binary=True)
        if len(Rel) <= 1:
            return rv
        Rel, nonRealRel = sift(rv.args, lambda i: all(s.is_real is not False
                                                      for s in i.free_symbols),
                               binary=True)
        Rel = [i.canonical for i in Rel]
        while changed and len(Rel) >= 2:
            changed = False
            # Sort based on ordered
            Rel = list(ordered(Rel))
            # Create a list of possible replacements
            results = []
            # Try all combinations
            for ((i, pi), (j, pj)) in combinations(enumerate(Rel), 2):
                for k, (pattern, simp) in enumerate(patterns):
                    res = []
                    # use SymPy matching
                    oldexpr = rv.func(pi, pj)
                    tmpres = oldexpr.match(pattern)
                    if tmpres:
                        res.append((tmpres, oldexpr))
                    # Try reversing first relational
                    # This and the rest should not be required with a better
                    # canonical
                    oldexpr = rv.func(pi.reversed, pj)
                    tmpres = oldexpr.match(pattern)
                    if tmpres:
                        res.append((tmpres, oldexpr))
                    # Try reversing second relational
                    oldexpr = rv.func(pi, pj.reversed)
                    tmpres = oldexpr.match(pattern)
                    if tmpres:
                        res.append((tmpres, oldexpr))
                    # Try reversing both relationals
                    oldexpr = rv.func(pi.reversed, pj.reversed)
                    tmpres = oldexpr.match(pattern)
                    if tmpres:
                        res.append((tmpres, oldexpr))

                    if res:
                        for tmpres, oldexpr in res:
                            # we have a matching, compute replacement
                            np = simp.subs(tmpres)
                            if np == dominatingvalue:
                                # if dominatingvalue, the whole expression
                                # will be replacementvalue
                                return replacementvalue
                            # add replacement
                            if not isinstance(np, ITE):
                                # We only want to use ITE replacements if
                                # they simplify to a relational
                                costsaving = measure(oldexpr) - measure(np)
                                if costsaving > 0:
                                    results.append((costsaving, (i, j, np)))
            if results:
                # Sort results based on complexity
                results = list(reversed(sorted(results,
                                               key=lambda pair: pair[0])))
                # Replace the one providing most simplification
                cost, replacement = results[0]
                i, j, newrel = replacement
                # Remove the old relationals
                del Rel[j]
                del Rel[i]
                if dominatingvalue is None or newrel != ~dominatingvalue:
                    # Insert the new one (no need to insert a value that will
                    # not affect the result)
                    Rel.append(newrel)
                # We did change something so try again
                changed = True

        rv = rv.func(*([_canonical(i) for i in ordered(Rel)]
                     +nonRel + nonRealRel))
        return rv

    @cacheit
    def _eval_domain_defined(self, x, **_):
        domain = Boolean._eval_domain_defined(self, x)
        for arg in self.args:
            domain &= arg.domain_defined(x)
        return domain


class And(LatticeOp, BooleanFunction):
    """
    Logical AND function.

    It evaluates its arguments in order, giving False immediately
    if any of them are False, and True if they are all True.

    Examples
    ========

    >>> from sympy.core import symbols
    >>> from sympy.abc import x, y
    >>> from sympy.logic.boolalg import And
    >>> x & y
    x & y

    Notes
    =====

    The ``&`` operator is provided as a convenience, but note that its use
    here is different from its normal use in Python, which is bitwise
    and. Hence, ``And(a, b)`` and ``a & b`` will return different things if
    ``a`` and ``b`` are integers.

    >>> And(x, y).subs(x, 1)
    y

    """

    def _print_LogOp(self, args, char):

        arg = args[0]
        if arg.is_Or:
            tex = r"\left(%s\right)" % self._print(arg)
        else:
            tex = r"%s" % self._print(arg)

        for arg in args[1:]:
            if arg.is_Boolean and not arg.is_Not:
                tex += r" %s \left(%s\right)" % (char, self._print(arg))
            else:
                tex += r" %s %s" % (char, self._print(arg))

        return tex

    def _sympystr(self, p):
        from sympy.printing.precedence import PRECEDENCE
        return p.stringify(self.args, " & ", PRECEDENCE["BitwiseAnd"])

    def _lean(self, p):
        from sympy.printing.precedence import PRECEDENCE
        return p.stringify(self.args, " \N{LOGICAL AND} ", PRECEDENCE["BitwiseAnd"])
    
    @classmethod
    def connected_equations(cls, args):
        child = {}
        parent = {}
        for lhs, rhs in args:
            if lhs in child:
                break
            child[lhs] = rhs
            
            if rhs in parent:
                break
            parent[rhs] = lhs
        else:
            root = lhs
            while root in parent:
                root = parent[root]
                
            next = root
            children = [next]
            while next in child:
                next = child[next]
                children.append(next)
             
            if len(children) == len(args) + 1:
                return children
        
    def _latex(self, p):
        if len(self.args) == 2:

            def render(op1, op2, a, x, b):
                a = p._print(a)
                b = p._print(b)
                x = p._print(x)
                return r"%s \%s %s \%s %s" % (a, op1, x, op2, b)
            
            eq1, eq2 = self.args
            if eq1.is_Less:
                a, x = eq1.args
                if eq2.is_Less:
                    _x, b = eq2.args
                    if x == _x: 
                        return render('lt', 'lt', a, x, b)
                    if a == b:
                        x, b, a = a, x, _x
                        return render('lt', 'lt', a, x, b)
                        
                if eq2.is_LessEqual:
                    _x, b = eq2.args
                    if x == _x:
                        return render('lt', 'le', a, x, b)
                    if a == b:
                        x, b, a = a, x, _x
                        return render('le', 'lt', a, x, b)
                    
            elif eq1.is_LessEqual:
                a, x = eq1.args
                if eq2.is_Less:
                    _x, b = eq2.args
                    if x == _x:
                        return render('le', 'lt', a, x, b)
                    if a == b:
                        x, b, a = a, x, _x
                        return render('lt', 'le', a, x, b)
                    
                if eq2.is_LessEqual:
                    _x, b = eq2.args
                    if x == _x:
                        return render('le', 'le', a, x, b)
                    if a == b:
                        x, b, a = a, x, _x
                        return render('le', 'le', a, x, b)
                    
            elif eq1.is_Greater:
                a, x = eq1.args
                if eq2.is_Greater:
                    _x, b = eq2.args
                    if x == _x:
                        return render('gt', 'gt', a, x, b)
                    if a == b:
                        x, b, a = a, x, _x
                        return render('gt', 'gt', a, x, b)
                    
                if eq2.is_GreaterEqual:
                    _x, b = eq2.args
                    if x == _x:
                        return render('gt', 'ge', a, x, b)
                    if a == b:
                        x, b, a = a, x, _x
                        return render('ge', 'gt', a, x, b)
                    
            elif eq1.is_GreaterEqual:
                a, x = eq1.args
                if eq2.is_Greater:
                    _x, b = eq2.args
                    if x == _x:
                        return render('ge', 'gt', a, x, b)
                    if a == b:
                        x, b, a = a, x, _x
                        return render('gt', 'ge', a, x, b)
                    
                if eq2.is_GreaterEqual:
                    _x, b = eq2.args
                    if x == _x:
                        return render('ge', 'ge', a, x, b)
                    if a == b:
                        x, b, a = a, x, _x
                        return render('ge', 'ge', a, x, b)

        args = []
        is_all_eq = True
        for arg in self.args:
            if arg.is_Or or arg.is_Conditioned:
                args.append(r"\left(%s\right)" % p._print(arg))
                is_all_eq = False
            else:
                args.append(p._print(arg))
                if not arg.is_Equal:
                    is_all_eq = False

        wedge = r'\wedge '
        if is_all_eq:
            conds = [eq.args for eq in self.args]
            children = And.connected_equations(conds)
            if children:
                return " = ".join([p._print(next) for next in children])
            if all(lhs.is_random and lhs.is_symbol and (rhs == lhs.var or rhs.is_Surrogate and rhs.arg == lhs) for lhs, rhs in conds):
                wedge = ','
            
        return wedge.join(args)

    def invert(self):
        return self.invert_type(*(arg.invert() for arg in self.args))

    def apply(self, axiom, *args, split=True, **kwargs):
        token = axiom.__name__.split(sep='.')
        i, type = inference_type(token)
        
        if type == 'of':
            if token[token.index('of') + 1].startswith('And'):
                split = False
            else:
                capitalWords = []
                for cond in token[i + 1:]:
                    if re.match('[A-Z]', cond):
                        capitalWords.append(cond)
                    else:
                        break
                if len(capitalWords) <= 1:
                    split = False

        elif type == 'to' or type == 'given':
            if token[2].startswith('And') or i == 3:
                split = False
        elif type in ('equ', 'Is'):
            split = split_and(axiom)
        if split:
            funcs = []
            
            depth = kwargs.pop('depth', None)
            if not depth:
                _args = [*self.args]
            else:
                _args = []

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
                        
            cond = axiom.apply(*_args, *args, **kwargs)
            if isinstance(cond, tuple): 
                clue = {f.clue for f in cond}
                assert len(clue) == 1
                [clue] = clue
                cond = And(*cond, **{clue: self})

            else:
                if cond.is_Equivalent and type in ('equ', 'Is'):
                    if cond.clue is None:
                        return cond.rhs
                
                clue = cond.clue
                cond.set_clause(clue, self, force=True)
                
            if cond.is_BooleanAtom:
                return cond.copy(**{clue: self})
            
            if kwargs.get('simplify', True):
                cond = cond.simplify()
            return cond
        else:
            return Boolean.apply(self, axiom, *args, **kwargs)

    def subs(self, *args, **kwargs):
        if all(isinstance(arg, Boolean) for arg in args):
            result = LatticeOp.subs(self, *args, **kwargs)
            if result.is_BooleanAtom:
                result = result.copy(equivalent=[self, *args])
            else:
                result.equivalent = [self, *args]
            return result
        
        if len(args) == 1:
            [dic] = args
            for old, new in dic.items():
                self = self._subs(old, new)
            return self

        old, new = args
        return self._subs(old, new)

    def __new__(cls, *args, evaluate=True, **options):
        valuable = set()
        for arg in args:
            if arg == True:
                continue
            if arg == False:
                return S.BooleanFalse.copy(**options)
            
            if arg.is_And:
                valuable |= arg._argset
            else:
                valuable.add(arg)

        args = valuable
        if len(args) == 0:
            return S.BooleanTrue.copy(**options)
        if len(args) == 1:
            [eq] = args
            if options:
                return eq.func(*eq.args, **options)
            return eq

        if evaluate and set(v.invert() for v in args) & args:
            return S.BooleanFalse.copy(**options)

        if options: 
            from sympy.core.inference import Inference
            return Inference(LatticeOp.__new__(cls, *args), **options)

        return LatticeOp.__new__(cls, *args, **options)

    nargs = None

    @classmethod
    def _need_to_be_raised(cls, self):
        return self == S.false

    @classmethod
    def _need_to_be_filtered(cls, self):
        return self == S.true

    @classmethod
    def _new_args_filter(cls, args):
        newargs = []
        rel = []

        for x in reversed(args):
            if x.is_Relational:
                c = x.canonical
                if c in rel:
                    continue
                nc = c.invert()
                nc = nc.canonical
                if any(r == nc for r in rel):
                    return [S.false]
                rel.append(c)
            newargs.append(x)
        return LatticeOp._new_args_filter(newargs, And)

    def _eval_simplify(self, ratio, measure, rational, inverse):
        from sympy.core.relational import Equal, Relational
        from sympy.solvers.solveset import linear_coeffs
        # standard simplify
        rv = super(And, self)._eval_simplify(
            ratio, measure, rational, inverse)
        if not isinstance(rv, And):
            return rv
        # simplify args that are equalities involving
        # symbols so x == 0 & x == y -> x==0 & y == 0
        Rel, nonRel = sift(rv.args, lambda i: isinstance(i, Relational),
                           binary=True)
        if not Rel:
            return rv
        eqs, other = sift(Rel, lambda i: isinstance(i, Equal), binary=True)
        if not eqs:
            return rv
        reps = {}
        sifted = {}
        if eqs:
            # group by length of free symbols
            sifted = sift(ordered([
                (i.free_symbols, i) for i in eqs]),
                lambda x: len(x[0]))
            eqs = []
            while 1 in sifted:
                for free, e in sifted.pop(1):
                    x = free.pop()
                    if e.lhs != x or x in e.rhs.free_symbols:
                        try:
                            m, b = linear_coeffs(
                                e.rewrite(Add, evaluate=False), x)
                            enew = e.func(x, -b / m)
                            if measure(enew) <= ratio * measure(e):
                                e = enew
                            else:
                                eqs.append(e)
                                continue
                        except ValueError:
                            pass
                    if x in reps:
                        eqs.append(e.func(e.rhs, reps[x]))
                    else:
                        reps[x] = e.rhs
                        eqs.append(e)
                resifted = defaultdict(list)
                for k in sifted:
                    for f, e in sifted[k]:
                        e = e.subs(reps)
                        f = e.free_symbols
                        resifted[len(f)].append((f, e))
                sifted = resifted
        for k in sifted:
            eqs.extend([e for f, e in sifted[k]])
        other = [ei.subs(reps) for ei in other]
        rv = rv.func(*([i.canonical for i in (eqs + other)] + nonRel))
        patterns = simplify_patterns_and()
        return self._apply_patternbased_simplification(rv, patterns,
                                                       measure, False)

    def _eval_as_set(self):
        from sympy.sets.sets import Intersection
        return Intersection(*[arg.as_set() for arg in self.args])

    def simplify(self, deep=False, **kwargs):
        dict_contains = defaultdict(set)
        dict_notcontains = defaultdict(set)
        dict_domain = defaultdict(set)
        for eq in self._argset:
            if eq.is_Element:
                e, S = eq.args
                dict_contains[e].add(eq)
            elif eq.is_NotElement:
                e, S = eq.args
                dict_notcontains[e].add(eq)
            elif eq.is_Relational:
                x, y = eq.args
                dict_domain[x].add(eq)
            elif eq.is_Or:
                if any(arg in self._argset for arg in eq.args):
                    return And(*self._argset - {eq}).simplify()
                
        from sympy.sets import Intersection, Element, NotElement, Union
        for e, eqs in dict_contains.items(): 
            if len(eqs) > 1: 
                sets = [contains.rhs for contains in eqs] 
                contains = Element(e, Intersection(*sets))
                argset = self._argset - eqs
                return self.func(*argset, contains)
            if e in dict_notcontains:
                _eqs = dict_notcontains[e]
                sets = [contains.rhs for contains in eqs]
                _sets = [contains.rhs for contains in _eqs]
                contains = Element(e, Intersection(*sets) - Union(*_sets))
                argset = self._argset - eqs - _eqs
                return self.func(*argset, contains)                
                
        for e, eqs in dict_notcontains.items(): 
            if len(eqs) > 1: 
                sets = [contains.rhs for contains in eqs] 
                eq = NotElement(e, Union(*sets))
                argset = self._argset - eqs
                return self.func(*argset, eq)
                            
        for e, eqs in dict_domain.items(): 
            if len(eqs) > 1:
                argset = self._argset - eqs
                eq, *eqs = eqs
                eq &= And(*eqs)
                if eq.is_And:
                    return self
                if eq.is_Element:
                    return self
                return self.func(*argset, eq).simplify()
                            
        return self

    def __and__(self, other):
        """Overloading for & operator"""
        if not other.is_bool and self.is_random and other.is_random:
            return self & other.as_boolean()

        lhs = tuple(self._argset)
        
        rhs = None
        if other.is_And:
            rhs = tuple(other._argset)
        elif other.is_Or:
            _self = self.invert()
            if _self in other._argset:
                args = set(other._argset)
                args.remove(_self)
                rhs = (other.func(*args),)

        if rhs is None:
            rhs = (other,)
        
        argset = set((*lhs, *rhs))
        args = [*argset]
        
        args_invert = set()
        for eq in args:
            args_invert.add(eq.invert())
                
        for ou_expr in args:
            if ou_expr.is_Or:
                if ou_expr._argset & args_invert:
                    ou = Or(*ou_expr._argset - args_invert)
                    argset.remove(ou_expr)
                    if ou.is_And: 
                        argset |= ou._argset
                    else:
                        argset.add(ou)                     
        
        return And(*argset)

    def __or__(self, other):
        if not other.is_bool and self.is_random and other.is_random:
            from sympy import Conditioned
            return Conditioned(self, other.as_boolean())

        if other.is_And:
            intersect = other._argset & self._argset
            if intersect:
                return And(*intersect, And(*self._argset - intersect) | And(*other._argset - intersect))
        return BooleanFunction.__or__(self, other)        

    def domain_conditioned(self, x):
        sol = x.domain
        for eq in self.args:
            sol &= x.domain_conditioned(eq)
        return sol

    @classmethod
    def simplify_ForAll(cls, self, function, *limits):
        res = self.simplify_int_limits(function)
        if res:
            function, limits = res
            return self.func(function, *limits).simplify()
        
        limits_cond = self.limits_cond
        if limits_cond.is_And:
            limits_cond = limits_cond._argset
        else:
            limits_cond = {limits_cond}
        for i, eq in enumerate(function.args):
            if eq in limits_cond:
                args = [*function.args]
                del args[i]
                function = cls(*args)
                return self.func(function, *limits).simplify()
        
    def copy(self, **kwargs):
        if kwargs:
            from sympy.core.inference import Inference
            return Inference(self, **kwargs)
        return self

    def _subs(self, old, new, **hints):
        if old.is_And:
            if not old._argset - self._argset:
                complement = self._argset - old._argset
                complement |= {new}
                return And(*complement)
        return LatticeOp._subs(self, old, new, **hints)

    @classmethod
    def class_key(cls):
        """Nice order of classes. """
        return 6, 0, cls.__name__


class Or(LatticeOp, BooleanFunction):
    """
    Logical OR function

    It evaluates its arguments in order, giving True immediately
    if any of them are True, and False if they are all False.

    Examples
    ========

    >>> from sympy.core import symbols
    >>> from sympy.abc import x, y
    >>> from sympy.logic.boolalg import Or
    >>> x | y
    x | y

    Notes
    =====

    The ``|`` operator is provided as a convenience, but note that its use
    here is different from its normal use in Python, which is bitwise
    or. Hence, ``Or(a, b)`` and ``a | b`` will return different things if
    ``a`` and ``b`` are integers.

    >>> Or(x, y).subs(x, 0)
    y

    """
    @classmethod
    def _need_to_be_raised(cls, self):
        return self == S.true

    @classmethod
    def _need_to_be_filtered(cls, self):
        return self == S.false
    
    def _latex(self, p):
        return p._print_LogOp(self.args, r"\vee")

    def _sympystr(self, p):
        from sympy.printing.precedence import PRECEDENCE
        return p.stringify(self.args, " | ", PRECEDENCE["BitwiseOr"])

    def _lean(self, p):
        from sympy.printing.precedence import PRECEDENCE
        return p.stringify(self.args, " \N{LOGICAL OR} ", PRECEDENCE["BitwiseOr"])

    def __new__(cls, *args, evaluate=True, **options):
        valuable = set()
        for arg in args:
            if arg == False:
                continue
            if arg == True:
                return S.BooleanTrue.copy(**options)
            
            if arg.is_Or:
                valuable |= arg._argset
            else:
                valuable.add(arg)

        if not valuable:
            return S.BooleanFalse.copy(**options)
        
        args = valuable
        if len(args) == 1:
            [eq] = args
            if options:
                return eq.func(*eq.args, evaluate=evaluate, **options)
            return eq

        if evaluate and set(v.invert() for v in args) & args:
            if 'plausible' in options:
                options['plausible'] = None
            else:
                return S.BooleanTrue.copy(**options)

        if options: 
            from sympy.core.inference import Inference
            return Inference(LatticeOp.__new__(cls, *args, evaluate=False), **options)
        return LatticeOp.__new__(cls, *args, evaluate=evaluate, **options)

    def invert(self):
        return self.invert_type(*(arg.invert() for arg in self.args))

    @classmethod
    def _new_args_filter(cls, args):
        newargs = []
        rel = []
#         args = BooleanFunction.binary_check_and_simplify(*args)
        for x in args:
            if x.is_Relational:
                c = x.canonical
                if c in rel:
                    continue
                nc = c.invert().canonical
                if any(r == nc for r in rel):
                    return [S.true]
                rel.append(c)
            newargs.append(x)
            
        return LatticeOp._new_args_filter(newargs, Or)

    def _eval_as_set(self):
        from sympy.sets.sets import Union
        return Union(*[arg.as_set() for arg in self.args])

    def _eval_simplify(self, ratio, measure, rational, inverse):
        # standard simplify
        rv = super(Or, self)._eval_simplify(ratio, measure, rational, inverse)
        if not isinstance(rv, Or):
            return rv
        patterns = simplify_patterns_or()
        return self._apply_patternbased_simplification(rv, patterns,
                                                       measure, S.true)

    def simplify(self, deep=False, **kwargs):
        if deep:
            return Boolean.simplify(self, deep, **kwargs)
        
        common_terms = None
        for eq in self._argset:
            if eq.is_And:
                if common_terms is None:
                    common_terms = eq._argset
                else:
                    common_terms &= eq._argset
            else:
                if common_terms is None:
                    common_terms = {eq}
                else:
                    common_terms &= {eq}
                    
            if not common_terms: 
                dict_contains = defaultdict(set)
                dict_notcontains = defaultdict(set)
                dict_domain = defaultdict(list)
                for eq in self._argset:
                    if eq.is_Element:
                        e, S = eq.args
                        dict_contains[e].add(eq)
                    elif eq.is_NotElement:
                        e, S = eq.args
                        dict_notcontains[e].add(eq)
                    elif eq.is_Relational:
                        x, y = eq.args
                        dict_domain[x].append(eq)
                        
                from sympy.sets import Intersection, Element, NotElement, Union
                for e, eqs in dict_contains.items(): 
                    if len(eqs) > 1: 
                        sets = [contains.rhs for contains in eqs] 
                        contains = Element(e, Union(*sets))
                        argset = self._argset - eqs
                        return self.func(*argset, contains)
                    if e in dict_notcontains:
                        _eqs = dict_notcontains[e]
                        sets = [contains.rhs for contains in eqs]
                        _sets = [contains.rhs for contains in _eqs]
                        contains = NotElement(e, Intersection(*_sets) - Union(*sets)).simplify()
                        argset = self._argset - eqs - _eqs
                        return self.func(*argset, contains)
                        
                for e, eqs in dict_notcontains.items(): 
                    if len(eqs) > 1: 
                        sets = [contains.rhs for contains in eqs] 
                        eq = NotElement(e, Intersection(*sets))
                        argset = self._argset - eqs
                        return self.func(*argset, eq)
                                    
                for e, eqs in dict_domain.items(): 
                    if len(eqs) > 1:
                        argset = self._argset - {*eqs}
                        for i in range(1, len(eqs)):
                            for j in range(i):
                                cond = eqs[i] | eqs[j]
                                if not cond.is_Or:
                                    del eqs[i]
                                    del eqs[j]
                                    eqs.append(cond)                                    
                                    return self.func(*argset, *eqs).simplify()
                                    
                return self
        
        eqs = []
        for eq in self._argset:
            if eq.is_And:
                eqs.append(And(*eq._argset - common_terms))
            else:
                return eq
                
        return And(self.func(*eqs), *common_terms)

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq = args[0]
            if isinstance(eq, dict):
                return LatticeOp.subs(eq)
            
            if eq.is_Quantifier:
                return self.bfn(self.subs, eq)
            
            if eq.is_Equal:
                old, new = eq.args
                if self.plausible:
                    eqs = []
                    for eq in self.args:
                        eqs.append(eq._subs(old, new) & eq.domain_definition())
                    return self.func(*eqs).copy(equivalent=self)
                else:
                    eq = self._subs(old, new)                
                    return eq.copy(equivalent=self)
        old, new = args
        if old.is_given:
            return self
        
        domain = self.domain_defined(old)
        if new.is_Number:
            assert new in domain
        else:
            if new.is_Symbol:
                if new.is_real:
                    if new.domain not in domain:
                        from sympy import NotElement
                        return Or(NotElement(new, domain), self._subs(old, new), equivalent=self)        
        
        result = LatticeOp.subs(self, *args, **kwargs)
        if all(isinstance(arg, Boolean) for arg in args): 
            result = result.copy(equivalent=[self, *args])            
        else: 
            result = result.copy(equivalent=self)
            
        return result

    def _subs(self, old, new, **hints):
        if old.is_Or:
            if not old._argset - self._argset:
                complement = self._argset - old._argset
                complement |= {new}
                return Or(*complement)
        return LatticeOp._subs(self, old, new, **hints)

    def __and__(self, other):
        this = self
        simplify = False
        if other.is_Or:
            args_intersection = self._argset & other._argset
            if args_intersection:
                lhs = Or(*self._argset - args_intersection)
                rhs = Or(*other._argset - args_intersection)
                
                return Or(*args_intersection, And(lhs, rhs))
        else:
            for eq in self._argset:
                if (other & eq).is_BooleanFalse:
                    args = set(self._argset)
                    args.remove(eq)
                    this = self.func(*args).simplify()
                    simplify = True
                    break

        if other.is_And:
            rhs = tuple(other._argset)
        else:
            rhs = (other,)
            
        this = And(this, *rhs)
        if simplify:
            this = this.simplify()
        return this

    def __or__(self, other):
        if other.is_Or:
            return BooleanFunction.__or__(self, other)
        return BooleanFunction.__or__(self, other)                

    @cacheit
    def _eval_domain_defined(self, x, **_):
        domain = x.emptySet
        for arg in self.args:
            domain |= arg.domain_defined(x)
        return domain

    def domain_conditioned(self, x):
        sol = x.emptySet
        for eq in self.args:
            sol |= x.domain_conditioned(eq)
        return x.domain & sol

    def copy(self, **kwargs):
        if kwargs:
            from sympy.core.inference import Inference
            return Inference(self, **kwargs)
        return self

    def domain_definition(self, **_):
        from sympy import Or
        return Or(*(arg.domain_definition() for arg in self.args))

    @classmethod
    def class_key(cls):
        """Nice order of classes. """
        return 6, 1, cls.__name__


And.invert_type = Or
Or.invert_type = And


class Not(BooleanFunction):
    """
    Logical Not function (negation)


    Returns True if the statement is False
    Returns False if the statement is True

    Examples
    ========

    >>> from sympy.logic.boolalg import Not, And, Or
    >>> from sympy.abc import x, A, B
    >>> Not(True)
    False
    >>> Not(False)
    True
    >>> Not(And(True, False))
    True
    >>> Not(Or(True, False))
    False
    >>> Not(And(And(True, x), Or(x, False)))
    ~x
    >>> ~x
    ~x
    >>> Not(And(Or(A, B), Or(~A, ~B)))
    ~((A | B) & (~A | ~B))

    Notes
    =====

    - The ``~`` operator is provided as a convenience, but note that its use
      here is different from its normal use in Python, which is bitwise
      not. In particular, ``~a`` and ``Not(a)`` will be different if ``a`` is
      an integer. Furthermore, since bools in Python subclass from ``int``,
      ``~True`` is the same as ``~1`` which is ``-2``, which has a boolean
      value of True.  To avoid this issue, use the SymPy boolean types
      ``true`` and ``false``.

    >>> from sympy import true
    >>> ~True
    -2
    >>> ~true
    False

    """

    @classmethod
    def eval(cls, arg, **options):
        if isinstance(arg, Number) or arg in (True, False):
            return false if arg else true
        if arg.is_Not:
            return arg.args[0]
        if arg.is_Relational:
            # Simplify Relational objects.
            return arg.invert_type(*arg.args, **options)
        if arg.is_LatticeOp:
            return arg.invert_type(*(~arg for arg in arg.args), **options)

    def _eval_as_set(self):
        """
        Rewrite logic operators and relationals in terms of real sets.

        Examples
        ========

        >>> from sympy import Not, Symbol
        >>> x = Symbol('x')
        >>> Not(x > 0).as_set()
        Interval(-oo, 0)
        """
        return self.args[0].as_set().complement(Reals)

    def to_nnf(self, simplify=True):
        if is_literal(self):
            return self

        expr = self.args[0]

        func, args = expr.func, expr.args

        if func == And:
            return Or._to_nnf(*[~arg for arg in args], simplify=simplify)

        if func == Or:
            return And._to_nnf(*[~arg for arg in args], simplify=simplify)

        if func == Imply:
            a, b = args
            return And._to_nnf(a, ~b, simplify=simplify)

        if func == Equivalent:
            return And._to_nnf(Or(*args), Or(*[~arg for arg in args]),
                               simplify=simplify)

        if func == Xor:
            result = []
            for i in range(1, len(args) + 1, 2):
                for neg in combinations(args, i):
                    clause = [~s if s in neg else s for s in args]
                    result.append(Or(*clause))
            return And._to_nnf(*result, simplify=simplify)

        if func == ITE:
            a, b, c = args
            return And._to_nnf(Or(a, ~c), Or(~a, ~b), simplify=simplify)

        raise ValueError("Illegal operator %s in expression" % func)
    
    def invert(self):
        return self.arg

    def _sympystr(self, p):
        from sympy.printing.precedence import PRECEDENCE
        return '~%s' % (p.parenthesize(self.arg, PRECEDENCE["Not"]))

    def _lean(self, p):
        from sympy.printing.precedence import PRECEDENCE
        return '~%s' % (p.parenthesize(self.arg, PRECEDENCE["Not"]))
    
    def _latex(self, p):
        cond = self.arg
        if isinstance(cond, Equivalent):
            return p._print_Equivalent(cond, r"\not\leftrightarrow")
        if isinstance(cond, Imply):
            return p._print_Imply(cond, r"\not\rightarrow")
        
        return r"\neg %s" % p._print(cond)


class Xor(BooleanFunction):
    """
    Logical XOR (exclusive OR) function.


    Returns True if an odd number of the arguments are True and the rest are
    False.

    Returns False if an even number of the arguments are True and the rest are
    False.

    Examples
    ========

    >>> from sympy.logic.boolalg import Xor
    >>> from sympy import symbols
    >>> x, y = symbols('x y')
    >>> Xor(True, False)
    True
    >>> Xor(True, True)
    False
    >>> Xor(True, False, True, True, False)
    True
    >>> Xor(True, False, True, False)
    False
    >>> x ^ y
    Xor(x, y)

    Notes
    =====

    The ``^`` operator is provided as a convenience, but note that its use
    here is different from its normal use in Python, which is bitwise xor. In
    particular, ``a ^ b`` and ``Xor(a, b)`` will be different if ``a`` and
    ``b`` are integers.

    >>> Xor(x, y).subs(y, 0)
    x

    """

    def __new__(cls, *args, **kwargs):
        argset = set([])
        obj = super(Xor, cls).__new__(cls, *args, **kwargs)
        for arg in obj._args:
            if isinstance(arg, Number) or arg in (True, False):
                if arg:
                    arg = true
                else:
                    continue
            if isinstance(arg, Xor):
                for a in arg.args:
                    argset.remove(a) if a in argset else argset.add(a)
            elif arg in argset:
                argset.remove(arg)
            else:
                argset.add(arg)
        rel = [(r, r.canonical, (~r).canonical)
               for r in argset if r.is_Relational]
        odd = False  # is number of complimentary pairs odd? start 0 -> False
        remove = []
        for i, (r, c, nc) in enumerate(rel):
            for j in range(i + 1, len(rel)):
                rj, cj = rel[j][:2]
                if cj == nc:
                    odd = ~odd
                    break
                elif cj == c:
                    break
            else:
                continue
            remove.append((r, rj))
        if odd:
            argset.remove(true) if true in argset else argset.add(true)
        for a, b in remove:
            argset.remove(a)
            argset.remove(b)
        if len(argset) == 0:
            return false
        elif len(argset) == 1:
            return argset.pop()
        elif True in argset:
            argset.remove(True)
            return Not(Xor(*argset))
        else:
            obj._args = tuple(ordered(argset))
            obj._argset = frozenset(argset)
            return obj

    @property
    @cacheit
    def args(self):
        return tuple(ordered(self._argset))

    def to_nnf(self, simplify=True):
        args = []
        for i in range(0, len(self.args) + 1, 2):
            for neg in combinations(self.args, i):
                clause = [~s if s in neg else s for s in self.args]
                args.append(Or(*clause))
        return And._to_nnf(*args, simplify=simplify)

    def _eval_simplify(self, ratio, measure, rational, inverse):
        # as standard simplify uses simplify_logic which writes things as
        # And and Or, we only simplify the partial expressions before using
        # patterns
        rv = self.func(*[a._eval_simplify(ratio=ratio, measure=measure,
                                          rational=rational, inverse=inverse)
                       for a in self.args])
        if not isinstance(rv, Xor):  # This shouldn't really happen here
            return rv
        patterns = simplify_patterns_xor()
        return self._apply_patternbased_simplification(rv, patterns,
                                                       measure, None)


class Nand(BooleanFunction):
    """
    Logical NAND function.

    It evaluates its arguments in order, giving True immediately if any
    of them are False, and False if they are all True.

    Returns True if any of the arguments are False
    Returns False if all arguments are True

    Examples
    ========

    >>> from sympy.logic.boolalg import Nand
    >>> from sympy import symbols
    >>> x, y = symbols('x y')
    >>> Nand(False, True)
    True
    >>> Nand(True, True)
    False
    >>> Nand(x, y)
    ~(x & y)

    """

    @classmethod
    def eval(cls, *args):
        return Not(And(*args))


class Nor(BooleanFunction):
    """
    Logical NOR function.

    It evaluates its arguments in order, giving False immediately if any
    of them are True, and True if they are all False.

    Returns False if any argument is True
    Returns True if all arguments are False

    Examples
    ========

    >>> from sympy.logic.boolalg import Nor
    >>> from sympy import symbols
    >>> x, y = symbols('x y')

    >>> Nor(True, False)
    False
    >>> Nor(True, True)
    False
    >>> Nor(False, True)
    False
    >>> Nor(False, False)
    True
    >>> Nor(x, y)
    ~(x | y)

    """

    @classmethod
    def eval(cls, *args):
        return Not(Or(*args))


class Xnor(BooleanFunction):
    """
    Logical XNOR function.

    Returns False if an odd number of the arguments are True and the rest are
    False.

    Returns True if an even number of the arguments are True and the rest are
    False.

    Examples
    ========

    >>> from sympy.logic.boolalg import Xnor
    >>> from sympy import symbols
    >>> x, y = symbols('x y')
    >>> Xnor(True, False)
    False
    >>> Xnor(True, True)
    True
    >>> Xnor(True, False, True, True, False)
    False
    >>> Xnor(True, False, True, False)
    True

    """

    @classmethod
    def eval(cls, *args):
        return Not(Xor(*args))

       
class Imply(BooleanAssumption):
    """
    Logical implication.

    A is Imply for B is equivalent to !A v B

    Accepts two Boolean arguments; A and B.
    Returns False if A is True and B is False
    Returns True otherwise.

    Examples
    ========

    >>> from sympy.logic.boolalg import Imply
    >>> from sympy import symbols
    >>> x, y = symbols('x y')

    >>> Imply(True, False)
    False
    >>> Imply(False, False)
    True
    >>> Imply(True, True)
    True
    >>> Imply(False, True)
    True
    >>> x >> y
    Imply(x, y)
    >>> y << x
    Imply(x, y)

    Notes
    =====

    The ``>>`` and ``<<`` operators are provided as a convenience, but note
    that their use here is different from their normal use in Python, which is
    bit shifts. Hence, ``Imply(a, b)`` and ``a >> b`` will return different
    things if ``a`` and ``b`` are integers.  In particular, since Python
    considers ``True`` and ``False`` to be integers, ``True >> True`` will be
    the same as ``1 >> 1``, i.e., 0, which has a truth value of False.  To
    avoid this issue, use the SymPy objects ``true`` and ``false``.

    >>> from sympy import true, false
    >>> True >> False
    1
    >>> true >> false
    False

    """
    # check if p => q holds?
    def __new__(cls, p, q, **assumptions):
        if assumptions.get('plausible') and p.is_Inference and q.is_Inference:
            if q.given_by(p):
                from sympy.core.inference import Inference
                return Inference(BinaryCondition.__new__(cls, p, q), plausible=None)
            
        return BinaryCondition.eval(cls, p, q, **assumptions)

    @classmethod
    def eval(cls, *args):
        try:
            newargs = []
            for x in args:
                if isinstance(x, Number) or x in (0, 1):
                    newargs.append(True if x else False)
                else:
                    newargs.append(x)
            A, B = newargs
        except ValueError:
            raise ValueError(
                "%d operand(s) used for an Imply "
                "(pairs are required): %s" % (len(args), str(args)))
            
        if B.is_BooleanFalse:
            return A.invert()
        
        if not A.is_symbol and not A.is_Function and A:
            return B
        
        if A.is_BooleanFalse or not B.is_symbol and not B.is_Function and B or A == B:
            return S.true
        
        if A.is_Relational and B.is_Relational:
            if A.canonical == B.canonical:
                return S.true
            if A.invert().canonical == B.canonical:
                return B
            
        if A.is_And:
            if B.is_And:
                if not B._argset - A._argset:
                    return S.true
            else:
                if B in A._argset:
                    return S.true
                
        if B.is_Or:
            if A.is_Or:
                if not A._argset - B._argset:
                    return S.true
            else:
                if A in B._argset:
                    return S.true

    def to_nnf(self, simplify=True):
        a, b = self.args
        return Or._to_nnf(~a, b, simplify=simplify)

    def _sympystr(self, p): 
        lhs, rhs = self.args
        _lhs = p._print(lhs)
        _rhs = p._print(rhs)
        if lhs.is_Inequality or lhs.is_And or lhs.is_Or:
            _lhs = f"({_lhs})"
            
        if rhs.is_Inequality or rhs.is_And or rhs.is_Or:
            _rhs = f"({_rhs})"
            
        return "%s >> %s" % (_lhs, _rhs)
    
    def _lean(self, p): 
        lhs, rhs = self.args
        _lhs = p._print(lhs)
        _rhs = p._print(rhs)
        if lhs.is_Equivalent:
            _lhs = f"({_lhs})"
            
        if rhs.is_Equivalent:
            _rhs = f"({_rhs})"

        return "%s \N{RIGHTWARDS ARROW} %s" % (_lhs, _rhs)

    def _latex(self, p, altchar=r'\rightarrow', rotate=False):
        A = p.conditions_wrapper(self.lhs, rotate=rotate)

        B = p.conditions_wrapper(self.rhs, rotate=rotate)
        
        if rotate:
            altchar = p.rotate_arrow(altchar)
            return r"\begin{array}{%s}%s\end{array}" % ('c', r'\\'.join([A, altchar, B]))      
        else: 
            return "%s %s %s" % (A, altchar, B)

    def _pretty(self, p, altchar=None):
        if p._use_unicode:
            return p._print_Boolean(self, altchar or u"\N{RIGHTWARDS DOUBLE ARROW}", sort=False)
        else:
            return p._print_Function(self)

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_Imply:
            if self.lhs == other.lhs:
                return self.func(self.lhs, self.rhs & other.rhs)
            if self.lhs == other.rhs:
                if self.rhs == other.lhs:
                    return Equivalent(self.lhs, self.rhs)
            if self.rhs == other.rhs:
                return Imply(self.lhs | other.lhs, self.rhs)
                
        elif other.is_Given:
            if self.lhs == other.lhs:
                if self.rhs == other.rhs:
                    return Equivalent(self.lhs, self.rhs)
                 
        return BinaryCondition.__and__(self, other)

    def premise_set(self):
        p = self.args[0]
        if p.is_And:
            return p, p._argset
        else:
            return p, {p}
          
    def simplify(self, **kwargs):
        q = self.args[1]
        
        if q.is_And:
            p, p_set = self.premise_set()
            
            eqs = []
            for eq in q.args: 
                if eq in p_set:
                    continue
                if eq.is_Or:
                    or_eqs = []
                    for e in eq.args:
                        if e in p_set:
                            continue
                        or_eqs.append(e)
                    if len(or_eqs) == len(eq.args):
                        eqs.append(eq)
                        continue
                    
                    if not or_eqs:
                        continue
                    
                    eq = Or(*or_eqs)  
                     
                eqs.append(eq)
                
            return Imply(p, And(*eqs))
        elif q.is_Or:
            p, p_set = self.premise_set()
            
            eqs = []
            for eq in q.args:
                if eq.is_And:
                    intersect = eq._argset & p_set
                    if intersect:
                        res = eq._argset - intersect
                        if res:
                            eq = And(*res)
                        else:
                            continue
                eqs.append(eq)
            return Imply(p, Or(*eqs))
            
        return self

    def inference_status(self, child):
        return child == 0

    def of(self, cls):
        res = Boolean.of(self, cls)
        if res is None:
            if cls.is_Given:
                args = cls.args
                if isinstance(args, property):
                    b, a = self.args
                    return a, b
                a, b = cls.args
                cls = Basic.__new__(Imply, b, a)
                res = Boolean.of(self, cls)
                if isinstance(res, tuple):
                    b, a = res
                    return a, b
            
        return res

Imply = Imply

class Given(BooleanAssumption):
    """
    Logical implication.

    A is Given for B is equivalent to A v !B

    Accepts two Boolean arguments; A and B.
    Returns False if A is True and B is False
    Returns True otherwise.

    """

    def __new__(cls, *args, **assumptions):
        return BinaryCondition.eval(cls, *args, **assumptions)

    @classmethod
    def eval(cls, *args):
        return Imply.eval(*args[::-1])

    def to_nnf(self, simplify=True):
        b, a = self.args
        return Or._to_nnf(a.invert(), b, simplify=simplify)

    def _sympystr(self, p):
        lhs, rhs = self.args
        _lhs = p._print(lhs)
        _rhs = p._print(rhs)
        if lhs.is_Inequality or lhs.is_And or lhs.is_Or:
            _lhs = f"({_lhs})"
            
        if rhs.is_Inequality or rhs.is_And or rhs.is_Or:
            _rhs = f"({_rhs})"
            
        return "%s << %s" % (_lhs, _rhs)

    def _lean(self, p):
        lhs, rhs = self.args
        _lhs = p._print(lhs)
        _rhs = p._print(rhs)
        if lhs.is_Inequality or lhs.is_And or lhs.is_Or:
            _lhs = f"({_lhs})"
            
        if rhs.is_Inequality or rhs.is_And or rhs.is_Or:
            _rhs = f"({_rhs})"
            
        return "%s \N{RIGHTWARDS ARROW} %s" % (_rhs, _lhs)

    def _pretty(self, p, altchar=None): 
        if p._use_unicode:
            return p._print_Boolean(self, altchar or u"\N{LEFTWARDS DOUBLE ARROW}", sort=False)
        else:
            return p._print_Function(self)
    
    def _latex(self, p, rotate=False):
        return Imply._latex(self, p, r'\Leftarrow', rotate=rotate)

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_Imply:
            if self.lhs == other.lhs:
                if self.rhs == other.rhs:
                    return Equivalent(self.lhs, self.rhs)
        elif other.is_Given:
            if self.lhs == other.lhs: 
                return Given(self.lhs, self.rhs | other.rhs)

        return BinaryCondition.__and__(self, other)

    def inference_status(self, child):
        return child == 1

    def of(self, cls):
        res = Boolean.of(self, cls)
        if res is None:
            if cls.is_Imply:
                args = cls.args
                if isinstance(args, property):
                    b, a = self.args
                    return a, b
                a, b = cls.args
                cls = Basic.__new__(Given, b, a)
                res = Boolean.of(self, cls)
                if isinstance(res, tuple):
                    b, a = res
                    return a, b
            
        return res


class Equivalent(BooleanAssumption):
    """
    Equivalence relation.

    Equivalent(A, B) is True iff A and B are both True or both False

    Returns True if all of the arguments are logically equivalent.
    Returns False otherwise.

    Examples
    ========

    >>> from sympy.logic.boolalg import Equivalent, And
    >>> from sympy.abc import x, y
    >>> Equivalent(False, False, False)
    True
    >>> Equivalent(True, False, False)
    False
    >>> Equivalent(x, And(x, True))
    True
    """

    def __new__(cls, *args, **assumptions):
        return BinaryCondition.eval(cls, *args, **assumptions)

    @classmethod
    def eval(cls, *args, **options):
        from sympy.core.relational import Relational
        args = [_sympify(arg) for arg in args]

        argset = set(args)
        for x in args:
            if isinstance(x, Number) or x in [True, False]:  # Includes 0, 1
                argset.discard(x)
                argset.add(True if x else False)
        rel = []
        for r in argset:
            if isinstance(r, Relational):
                rel.append((r, r.canonical, r.invert().canonical))
        remove = []
        for i, (r, c, nc) in enumerate(rel):
            for j in range(i + 1, len(rel)):
                rj, cj = rel[j][:2]
                if cj == nc:
                    return false
                elif cj == c:
                    remove.append((r, rj))
                    break
        for a, b in remove:
            argset.remove(a)
            argset.remove(b)
            argset.add(True)
        if len(argset) <= 1:
            if 'plausible' in options:
                eq, *_ = argset
                del options['plausible']
                return BinaryCondition.__new__(cls, eq, eq)
            return S.true.copy(**options)
        if True in argset:
            argset.discard(True)
            return And(*argset)
        if False in argset:
            argset.discard(False)
            return And(*[arg.invert() for arg in argset])

    def to_nnf(self, simplify=True):
        args = []
        for a, b in zip(self.args, self.args[1:]):
            args.append(Or(~a, b))
        args.append(Or(~self.args[-1], self.args[0]))
        return And._to_nnf(*args, simplify=simplify)

    def _sympystr(self, p):
        return "Equivalent(%s, %s)" % (p._print(self.lhs), p._print(self.rhs))

    def _lean(self, p):
        return "%s \N{LEFT RIGHT ARROW} %s" % (p._print(self.lhs), p._print(self.rhs))

    def _latex(self, p, rotate=False):
        return Imply._latex(self, p, r'\leftrightarrow', rotate=rotate)

    def inference_status(self, child):
        raise Exception("boolean conditions within Equivalent are not applicable for inequivalent inference!")       

Iff = Equivalent


class NotImply(BooleanAssumption):

    def __new__(cls, *args, **assumptions):
        return BinaryCondition.eval(cls, *args, **assumptions)

    @classmethod
    def eval(cls, *args):
        ...
        
    def _sympystr(self, p):
        return "NotImply(%s, %s)" % (p._print(self.lhs), p._print(self.rhs))
    
    def _lean(self, p):
        return "%s \N{RIGHTWARDS DOUBLE ARROW WITH STROKE} %s" % (p._print(self.lhs), p._print(self.rhs))
    
    def _latex(self, p, rotate=False):
        A = p.conditions_wrapper(self.lhs)
        B = p.conditions_wrapper(self.rhs)
        return r"%s \nRightarrow %s" % (A, B)

    def __and__(self, other):
        return BinaryCondition.__and__(self, other)

    def inference_status(self, child):
        return child == 1

NotImply = NotImply

class NotGiven(BooleanAssumption):
    
    @classmethod
    def eval(cls, *args):
        ...

    def _sympystr(self, p):
        return "NotGiven(%s, %s)" % (p._print(self.lhs), p._print(self.rhs))

    def _lean(self, p):
        return "%s \N{LEFTWARDS DOUBLE ARROW WITH STROKE} %s" % (p._print(self.lhs), p._print(self.rhs))

    def _latex(self, p, altchar='\nLeftarrow', rotate=False):
        return Imply._latex(self, p, altchar, rotate=rotate)

    def inference_status(self, child):
        return child == 0


class NotIff(BooleanAssumption):

    def _sympystr(self, p):
        return "NotIff(%s, %s)" % (p._print(self.lhs), p._print(self.rhs))

    def _lean(self, p):
        return "%s \N{LEFT RIGHT DOUBLE ARROW WITH STROKE} %s" % (p._print(self.lhs), p._print(self.rhs))
    
    def _latex(self, p, altchar='\nLeftrightarrow', rotate=False):
        return Imply._latex(self, p, altchar, rotate=rotate)

    def inference_status(self, child):
        raise Exception("boolean conditions within NotIff are not applicable for inequivalent inference!")       


Imply.reversed_type = Given
Given.reversed_type = Imply
Equivalent.reversed_type = Equivalent

NotImply.reversed_type = NotGiven
NotGiven.reversed_type = NotImply
NotIff.reversed_type = NotIff

Imply.invert_type = NotImply
Given.invert_type = NotGiven
Equivalent.invert_type = NotIff

NotImply.invert_type = Imply
NotGiven.invert_type = Given
NotIff.invert_type = Equivalent


class ITE(BooleanFunction):
    """
    If then else clause.

    ITE(A, B, C) evaluates and returns the result of B if A is true
    else it returns the result of C. All args must be Booleans.

    Examples
    ========

    >>> from sympy.logic.boolalg import ITE, And, Xor, Or
    >>> from sympy.abc import x, y, z
    >>> ITE(True, False, True)
    False
    >>> ITE(Or(True, False), And(True, True), Xor(True, True))
    True
    >>> ITE(x, y, z)
    ITE(x, y, z)
    >>> ITE(True, x, y)
    x
    >>> ITE(False, x, y)
    y
    >>> ITE(x, y, y)
    y

    Trying to use non-Boolean args will generate a TypeError:

    >>> ITE(True, [], ())
    Traceback (most recent call last):
    ...
    TypeError: expecting bool, Boolean or ITE, not `[]`

    """

    def __new__(cls, *args, **kwargs):
        from sympy.core.relational import Eq, Ne
        if len(args) != 3:
            raise ValueError('expecting exactly 3 args')
        a, b, c = args
        # check use of binary symbols
        if isinstance(a, (Eq, Ne)):
            # in this context, we can evaluate the Eq/Ne
            # if one arg is a binary symbol and the other
            # is true/false
            b, c = map(as_Boolean, (b, c))
            binary_symbols = set().union(*[i.binary_symbols for i in (b, c)])
            if len(set(a.args) - binary_symbols) == 1:
                # one arg is a binary_symbols
                _a = a
                if a.lhs is S.true:
                    a = a.rhs
                elif a.rhs is S.true:
                    a = a.lhs
                elif a.lhs is S.false:
                    a = ~a.rhs
                elif a.rhs is S.false:
                    a = ~a.lhs
                else:
                    # binary can only equal True or False
                    a = S.false
                if isinstance(_a, Ne):
                    a = ~a
        else:
            a, b, c = BooleanFunction.binary_check_and_simplify(
                a, b, c)
        rv = None
        if kwargs.get('evaluate', True):
            rv = cls.eval(a, b, c)
        if rv is None:
            rv = BooleanFunction.__new__(cls, a, b, c, evaluate=False)
        return rv

    @classmethod
    def eval(cls, *args):
        from sympy.core.relational import Eq, Ne
        # do the args give a singular result?
        a, b, c = args
        if isinstance(a, (Ne, Eq)):
            _a = a
            if S.true in a.args:
                a = a.lhs if a.rhs is S.true else a.rhs
            elif S.false in a.args:
                a = ~a.lhs if a.rhs is S.false else ~a.rhs
            else:
                _a = None
            if _a is not None and isinstance(_a, Ne):
                a = ~a
        if a is S.true:
            return b
        if a is S.false:
            return c
        if b == c:
            return b
        else:
            # or maybe the results allow the answer to be expressed
            # in terms of the condition
            if b is S.true and c is S.false:
                return a
            if b is S.false and c is S.true:
                return Not(a)
        if [a, b, c] != args:
            return cls(a, b, c, evaluate=False)

    def to_nnf(self, simplify=True):
        a, b, c = self.args
        return And._to_nnf(Or(~a, b), Or(a, c), simplify=simplify)

    def _eval_as_set(self):
        return self.to_nnf().as_set()

    def _eval_rewrite_as_Piecewise(self, *args, **kwargs):
        from sympy.functions import Piecewise
        return Piecewise((args[1], args[0]), (args[2], True))

# end class definitions. Some useful methods


def conjuncts(expr):
    """Return a list of the conjuncts in the expr s.

    Examples
    ========

    >>> from sympy.logic.boolalg import conjuncts
    >>> from sympy.abc import A, B
    >>> conjuncts(A & B)
    frozenset({A, B})
    >>> conjuncts(A | B)
    frozenset({A | B})

    """
    return And.make_args(expr)


def disjuncts(expr):
    """Return a list of the disjuncts in the sentence s.

    Examples
    ========

    >>> from sympy.logic.boolalg import disjuncts
    >>> from sympy.abc import A, B
    >>> disjuncts(A | B)
    frozenset({A, B})
    >>> disjuncts(A & B)
    frozenset({A & B})

    """
    return Or.make_args(expr)


def distribute_and_over_or(expr):
    """
    Given a sentence s consisting of conjunctions and disjunctions
    of literals, return an equivalent sentence in CNF.

    Examples
    ========

    >>> from sympy.logic.boolalg import distribute_and_over_or, And, Or, Not
    >>> from sympy.abc import A, B, C
    >>> distribute_and_over_or(Or(A, And(Not(B), Not(C))))
    (A | ~B) & (A | ~C)
    """
    return _distribute((expr, And, Or))


def distribute_or_over_and(expr):
    """
    Given a sentence s consisting of conjunctions and disjunctions
    of literals, return an equivalent sentence in DNF.

    Note that the output is NOT simplified.

    Examples
    ========

    >>> from sympy.logic.boolalg import distribute_or_over_and, And, Or, Not
    >>> from sympy.abc import A, B, C
    >>> distribute_or_over_and(And(Or(Not(A), B), C))
    (B & C) | (C & ~A)
    """
    return _distribute((expr, Or, And))


def _distribute(info):
    """
    Distributes info[1] over info[2] with respect to info[0].
    """
    if isinstance(info[0], info[2]):
        for arg in info[0].args:
            if isinstance(arg, info[1]):
                conj = arg
                break
        else:
            return info[0]
        rest = info[2](*[a for a in info[0].args if a is not conj])
        return info[1](*list(map(_distribute,
                                 [(info[2](c, rest), info[1], info[2])
                                  for c in conj.args])))
    elif isinstance(info[0], info[1]):
        return info[1](*list(map(_distribute,
                                 [(x, info[1], info[2])
                                  for x in info[0].args])))
    else:
        return info[0]


def to_nnf(expr, simplify=True):
    """
    Converts expr to Negation Normal Form.
    A logical expression is in Negation Normal Form (NNF) if it
    contains only And, Or and Not, and Not is applied only to literals.
    If simplify is True, the result contains no redundant clauses.

    Examples
    ========

    >>> from sympy.abc import A, B, C, D
    >>> from sympy.logic.boolalg import Not, Equivalent, to_nnf
    >>> to_nnf(Not((~A & ~B) | (C & D)))
    (A | B) & (~C | ~D)
    >>> to_nnf(Equivalent(A >> B, B >> A))
    (A | ~B | (A & ~B)) & (B | ~A | (B & ~A))
    """
    if is_nnf(expr, simplify):
        return expr
    return expr.to_nnf(simplify)


def to_cnf(expr, simplify=False):
    """
    Convert a propositional logical sentence s to conjunctive normal form.
    That is, of the form ((A | ~B | ...) & (B | C | ...) & ...)
    If simplify is True, the expr is evaluated to its simplest CNF form  using
    the Quine-McCluskey algorithm.

    Examples
    ========

    >>> from sympy.logic.boolalg import to_cnf
    >>> from sympy.abc import A, B, D
    >>> to_cnf(~(A | B) | D)
    (D | ~A) & (D | ~B)
    >>> to_cnf((A | B) & (A | ~A), True)
    A | B

    """
    expr = sympify(expr)
    if not isinstance(expr, BooleanFunction):
        return expr

    if simplify:
        return simplify_logic(expr, 'cnf', True)

    # Don't convert unless we have to
    if is_cnf(expr):
        return expr

    expr = eliminate_implications(expr)
    return distribute_and_over_or(expr)


def to_dnf(expr, simplify=False):
    """
    Convert a propositional logical sentence s to disjunctive normal form.
    That is, of the form ((A & ~B & ...) | (B & C & ...) | ...)
    If simplify is True, the expr is evaluated to its simplest DNF form using
    the Quine-McCluskey algorithm.

    Examples
    ========

    >>> from sympy.logic.boolalg import to_dnf
    >>> from sympy.abc import A, B, C
    >>> to_dnf(B & (A | C))
    (A & B) | (B & C)
    >>> to_dnf((A & B) | (A & ~B) | (B & C) | (~B & C), True)
    A | C

    """
    expr = sympify(expr)
    if not isinstance(expr, BooleanFunction):
        return expr

    if simplify:
        return simplify_logic(expr, 'dnf', True)

    # Don't convert unless we have to
    if is_dnf(expr):
        return expr

    expr = eliminate_implications(expr)
    return distribute_or_over_and(expr)


def is_nnf(expr, simplified=True):
    """
    Checks if expr is in Negation Normal Form.
    A logical expression is in Negation Normal Form (NNF) if it
    contains only And, Or and Not, and Not is applied only to literals.
    If simpified is True, checks if result contains no redundant clauses.

    Examples
    ========

    >>> from sympy.abc import A, B, C
    >>> from sympy.logic.boolalg import Not, is_nnf
    >>> is_nnf(A & B | ~C)
    True
    >>> is_nnf((A | ~A) & (B | C))
    False
    >>> is_nnf((A | ~A) & (B | C), False)
    True
    >>> is_nnf(Not(A & B) | C)
    False
    >>> is_nnf((A >> B) & (B >> A))
    False
    """

    expr = sympify(expr)
    if is_literal(expr):
        return True

    stack = [expr]

    while stack:
        expr = stack.pop()
        if expr.func in (And, Or):
            if simplified:
                args = expr.args
                for arg in args:
                    if Not(arg) in args:
                        return False
            stack.extend(expr.args)

        elif not is_literal(expr):
            return False

    return True


def is_cnf(expr):
    """
    Test whether or not an expression is in conjunctive normal form.

    Examples
    ========

    >>> from sympy.logic.boolalg import is_cnf
    >>> from sympy.abc import A, B, C
    >>> is_cnf(A | B | C)
    True
    >>> is_cnf(A & B & C)
    True
    >>> is_cnf((A & B) | C)
    False

    """
    return _is_form(expr, And, Or)


def is_dnf(expr):
    """
    Test whether or not an expression is in disjunctive normal form.

    Examples
    ========

    >>> from sympy.logic.boolalg import is_dnf
    >>> from sympy.abc import A, B, C
    >>> is_dnf(A | B | C)
    True
    >>> is_dnf(A & B & C)
    True
    >>> is_dnf((A & B) | C)
    True
    >>> is_dnf(A & (B | C))
    False

    """
    return _is_form(expr, Or, And)


def _is_form(expr, function1, function2):
    """
    Test whether or not an expression is of the required form.

    """
    expr = sympify(expr)

    # Special case of an Atom
    if expr.is_Atom:
        return True

    # Special case of a single expression of function2
    if isinstance(expr, function2):
        for lit in expr.args:
            if isinstance(lit, Not):
                if not lit.args[0].is_Atom:
                    return False
            else:
                if not lit.is_Atom:
                    return False
        return True

    # Special case of a single negation
    if isinstance(expr, Not):
        if not expr.args[0].is_Atom:
            return False

    if not isinstance(expr, function1):
        return False

    for cls in expr.args:
        if cls.is_Atom:
            continue
        if isinstance(cls, Not):
            if not cls.args[0].is_Atom:
                return False
        elif not isinstance(cls, function2):
            return False
        for lit in cls.args:
            if isinstance(lit, Not):
                if not lit.args[0].is_Atom:
                    return False
            else:
                if not lit.is_Atom:
                    return False

    return True


def eliminate_implications(expr):
    """
    Change >>, <<, and Equivalent into &, |, and ~. That is, return an
    expression that is equivalent to s, but has only &, |, and ~ as logical
    operators.

    Examples
    ========

    >>> from sympy.logic.boolalg import Imply, Equivalent, \
         eliminate_implications
    >>> from sympy.abc import A, B, C
    >>> eliminate_implications(Imply(A, B))
    B | ~A
    >>> eliminate_implications(Equivalent(A, B))
    (A | ~B) & (B | ~A)
    >>> eliminate_implications(Equivalent(A, B, C))
    (A | ~C) & (B | ~A) & (C | ~B)
    """
    return to_nnf(expr, simplify=False)


def is_literal(expr):
    """
    Returns True if expr is a literal, else False.

    Examples
    ========

    >>> from sympy import Or, Q
    >>> from sympy.abc import A, B
    >>> from sympy.logic.boolalg import is_literal
    >>> is_literal(A)
    True
    >>> is_literal(~A)
    True
    >>> is_literal(Q.zero(A))
    True
    >>> is_literal(A + B)
    True
    >>> is_literal(Or(A, B))
    False
    """
    if isinstance(expr, Not):
        return not isinstance(expr.args[0], BooleanFunction)
    else:
        return not isinstance(expr, BooleanFunction)


def to_int_repr(clauses, symbols):
    """
    Takes clauses in CNF format and puts them into an integer representation.

    Examples
    ========

    >>> from sympy.logic.boolalg import to_int_repr
    >>> from sympy.abc import x, y
    >>> to_int_repr([x | y, y], [x, y]) == [{1, 2}, {2}]
    True

    """

    # Convert the symbol list into a dict
    symbols = dict(list(zip(symbols, list(range(1, len(symbols) + 1)))))

    def append_symbol(arg, symbols):
        if isinstance(arg, Not):
            return -symbols[arg.args[0]]
        else:
            return symbols[arg]

    return [set(append_symbol(arg, symbols) for arg in Or.make_args(c))
            for c in clauses]


def term_to_integer(term):
    """
    Return an integer corresponding to the base-2 digits given by ``term``.

    Parameters
    ==========

    term : a string or list of ones and zeros

    Examples
    ========

    >>> from sympy.logic.boolalg import term_to_integer
    >>> term_to_integer([1, 0, 0])
    4
    >>> term_to_integer('100')
    4

    """

    return int(''.join(list(map(str, list(term)))), 2)


def integer_to_term(k, n_bits=None):
    """
    Return a list of the base-2 digits in the integer, ``k``.

    Parameters
    ==========

    k : int
    n_bits : int
        If ``n_bits`` is given and the number of digits in the binary
        representation of ``k`` is smaller than ``n_bits`` then left-pad the
        list with 0s.

    Examples
    ========

    >>> from sympy.logic.boolalg import integer_to_term
    >>> integer_to_term(4)
    [1, 0, 0]
    >>> integer_to_term(4, 6)
    [0, 0, 0, 1, 0, 0]
    """

    s = '{0:0{1}b}'.format(abs(as_int(k)), as_int(abs(n_bits or 0)))
    return list(map(int, s))


def truth_table(expr, variables, input=True):
    """
    Return a generator of all possible configurations of the input variables,
    and the result of the boolean expression for those values.

    Parameters
    ==========

    expr : string or boolean expression
    variables : list of variables
    input : boolean (default True)
        indicates whether to return the input combinations.

    Examples
    ========

    >>> from sympy.logic.boolalg import truth_table
    >>> from sympy.abc import x,y
    >>> table = truth_table(x >> y, [x, y])
    >>> for t in table:
    ...     print('{0} -> {1}'.format(*t))
    [0, 0] -> True
    [0, 1] -> True
    [1, 0] -> False
    [1, 1] -> True

    >>> table = truth_table(x | y, [x, y])
    >>> list(table)
    [([0, 0], False), ([0, 1], True), ([1, 0], True), ([1, 1], True)]

    If input is false, truth_table returns only a list of truth values.
    In this case, the corresponding input values of variables can be
    deduced from the index of a given output.

    >>> from sympy.logic.boolalg import integer_to_term
    >>> vars = [y, x]
    >>> values = truth_table(x >> y, vars, input=False)
    >>> values = list(values)
    >>> values
    [True, False, True, True]

    >>> for i, value in enumerate(values):
    ...     print('{0} -> {1}'.format(list(zip(
    ...     vars, integer_to_term(i, len(vars)))), value))
    [(y, 0), (x, 0)] -> True
    [(y, 0), (x, 1)] -> False
    [(y, 1), (x, 0)] -> True
    [(y, 1), (x, 1)] -> True

    """
    variables = [sympify(v) for v in variables]

    expr = sympify(expr)
    if not isinstance(expr, BooleanFunction) and not is_literal(expr):
        return

    table = product([0, 1], repeat=len(variables))
    for term in table:
        term = list(term)
        value = expr.xreplace(dict(zip(variables, term)))

        if input:
            yield term, value
        else:
            yield value


def _check_pair(minterm1, minterm2):
    """
    Checks if a pair of minterms differs by only one bit. If yes, returns
    index, else returns -1.
    """
    index = -1
    for x, (i, j) in enumerate(zip(minterm1, minterm2)):
        if i != j:
            if index == -1:
                index = x
            else:
                return -1
    return index


def _convert_to_varsSOP(minterm, variables):
    """
    Converts a term in the expansion of a function from binary to its
    variable form (for SOP).
    """
    temp = []
    for i, m in enumerate(minterm):
        if m == 0:
            temp.append(Not(variables[i]))
        elif m == 1:
            temp.append(variables[i])
        else:
            pass  # ignore the 3s
    return And(*temp)


def _convert_to_varsPOS(maxterm, variables):
    """
    Converts a term in the expansion of a function from binary to its
    variable form (for POS).
    """
    temp = []
    for i, m in enumerate(maxterm):
        if m == 1:
            temp.append(Not(variables[i]))
        elif m == 0:
            temp.append(variables[i])
        else:
            pass  # ignore the 3s
    return Or(*temp)


def _simplified_pairs(terms):
    """
    Reduces a set of minterms, if possible, to a simplified set of minterms
    with one less variable in the terms using QM method.
    """
    simplified_terms = []
    todo = list(range(len(terms)))
    for i, ti in enumerate(terms[:-1]):
        for j_i, tj in enumerate(terms[(i + 1):]):
            index = _check_pair(ti, tj)
            if index != -1:
                todo[i] = todo[j_i + i + 1] = None
                newterm = ti[:]
                newterm[index] = 3
                if newterm not in simplified_terms:
                    simplified_terms.append(newterm)
    simplified_terms.extend(
        [terms[i] for i in [_ for _ in todo if _ is not None]])
    return simplified_terms


def _compare_term(minterm, term):
    """
    Return True if a binary term is satisfied by the given term. Used
    for recognizing prime implicants.
    """
    for i, x in enumerate(term):
        if x != 3 and x != minterm[i]:
            return False
    return True


def _rem_redundancy(l1, terms):
    """
    After the truth table has been sufficiently simplified, use the prime
    implicant table method to recognize and eliminate redundant pairs,
    and return the essential arguments.
    """

    if len(terms):
        # Create dominating matrix
        dommatrix = [[0] * len(l1) for n in range(len(terms))]
        for primei, prime in enumerate(l1):
            for termi, term in enumerate(terms):
                if _compare_term(term, prime):
                    dommatrix[termi][primei] = 1

        # Non-dominated prime implicants, dominated set to None
        ndprimeimplicants = list(range(len(l1)))
        # Non-dominated terms, dominated set to None
        ndterms = list(range(len(terms)))

        # Mark dominated rows and columns
        oldndterms = None
        oldndprimeimplicants = None
        while ndterms != oldndterms or \
                ndprimeimplicants != oldndprimeimplicants:
            oldndterms = ndterms[:]
            oldndprimeimplicants = ndprimeimplicants[:]
            for rowi, row in enumerate(dommatrix):
                if ndterms[rowi] is not None:
                    row = [row[i] for i in
                           [_ for _ in ndprimeimplicants if _ is not None]]
                    for row2i, row2 in enumerate(dommatrix):
                        if rowi != row2i and ndterms[row2i] is not None:
                            row2 = [row2[i] for i in
                                    [_ for _ in ndprimeimplicants
                                     if _ is not None]]
                            if all(a >= b for (a, b) in zip(row2, row)):
                                # row2 dominating row, keep row
                                ndterms[row2i] = None
            for coli in range(len(l1)):
                if ndprimeimplicants[coli] is not None:
                    col = [dommatrix[a][coli] for a in range(len(terms))]
                    col = [col[i] for i in
                           [_ for _ in oldndterms if _ is not None]]
                    for col2i in range(len(l1)):
                        if coli != col2i and \
                                ndprimeimplicants[col2i] is not None:
                            col2 = [dommatrix[a][col2i]
                                    for a in range(len(terms))]
                            col2 = [col2[i] for i in
                                    [_ for _ in oldndterms if _ is not None]]
                            if all(a >= b for (a, b) in zip(col, col2)):
                                # col dominating col2, keep col
                                ndprimeimplicants[col2i] = None
        l1 = [l1[i] for i in [_ for _ in ndprimeimplicants if _ is not None]]

        return l1
    else:
        return []


def _input_to_binlist(inputlist, variables):
    binlist = []
    bits = len(variables)
    for val in inputlist:
        if isinstance(val, int):
            binlist.append(ibin(val, bits))
        elif isinstance(val, dict):
            nonspecvars = list(variables)
            for key in val.keys():
                nonspecvars.remove(key)
            for t in product([0, 1], repeat=len(nonspecvars)):
                d = dict(zip(nonspecvars, t))
                d.update(val)
                binlist.append([d[v] for v in variables])
        elif isinstance(val, (list, tuple)):
            if len(val) != bits:
                raise ValueError("Each term must contain {} bits as there are"
                                 "\n{} variables (or be an integer)."
                                 "".format(bits, bits))
            binlist.append(list(val))
        else:
            raise TypeError("A term list can only contain lists,"
                            " ints or dicts.")
    return binlist


def SOPform(variables, minterms, dontcares=None):
    """
    The SOPform function uses simplified_pairs and a redundant group-
    eliminating algorithm to convert the list of all input combos that
    generate '1' (the minterms) into the smallest Sum of Products form.

    The variables must be given as the first argument.

    Return a logical Or function (i.e., the "sum of products" or "SOP"
    form) that gives the desired outcome. If there are inputs that can
    be ignored, pass them as a list, too.

    The result will be one of the (perhaps many) functions that satisfy
    the conditions.

    Examples
    ========

    >>> from sympy.logic import SOPform
    >>> from sympy import symbols
    >>> w, x, y, z = symbols('w x y z')
    >>> minterms = [[0, 0, 0, 1], [0, 0, 1, 1],
    ...             [0, 1, 1, 1], [1, 0, 1, 1], [1, 1, 1, 1]]
    >>> dontcares = [[0, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 1]]
    >>> SOPform([w, x, y, z], minterms, dontcares)
    (y & z) | (z & ~w)

    The terms can also be represented as integers:

    >>> minterms = [1, 3, 7, 11, 15]
    >>> dontcares = [0, 2, 5]
    >>> SOPform([w, x, y, z], minterms, dontcares)
    (y & z) | (z & ~w)

    They can also be specified using dicts, which does not have to be fully
    specified:

    >>> minterms = [{w: 0, x: 1}, {y: 1, z: 1, x: 0}]
    >>> SOPform([w, x, y, z], minterms)
    (x & ~w) | (y & z & ~x)

    Or a combination:

    >>> minterms = [4, 7, 11, [1, 1, 1, 1]]
    >>> dontcares = [{w : 0, x : 0, y: 0}, 5]
    >>> SOPform([w, x, y, z], minterms, dontcares)
    (w & y & z) | (x & y & z) | (~w & ~y)

    References
    ==========

    .. [1] en.wikipedia.org/wiki/Quine-McCluskey_algorithm

    """
    variables = [sympify(v) for v in variables]
    if minterms == []:
        return false

    minterms = _input_to_binlist(minterms, variables)
    dontcares = _input_to_binlist((dontcares or []), variables)
    for d in dontcares:
        if d in minterms:
            raise ValueError('%s in minterms is also in dontcares' % d)

    old = None
    new = minterms + dontcares
    while new != old:
        old = new
        new = _simplified_pairs(old)
    essential = _rem_redundancy(new, minterms)
    return Or(*[_convert_to_varsSOP(x, variables) for x in essential])


def POSform(variables, minterms, dontcares=None):
    """
    The POSform function uses simplified_pairs and a redundant-group
    eliminating algorithm to convert the list of all input combinations
    that generate '1' (the minterms) into the smallest Product of Sums form.

    The variables must be given as the first argument.

    Return a logical And function (i.e., the "product of sums" or "POS"
    form) that gives the desired outcome. If there are inputs that can
    be ignored, pass them as a list, too.

    The result will be one of the (perhaps many) functions that satisfy
    the conditions.

    Examples
    ========

    >>> from sympy.logic import POSform
    >>> from sympy import symbols
    >>> w, x, y, z = symbols('w x y z')
    >>> minterms = [[0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 1, 1],
    ...             [1, 0, 1, 1], [1, 1, 1, 1]]
    >>> dontcares = [[0, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 1]]
    >>> POSform([w, x, y, z], minterms, dontcares)
    z & (y | ~w)

    The terms can also be represented as integers:

    >>> minterms = [1, 3, 7, 11, 15]
    >>> dontcares = [0, 2, 5]
    >>> POSform([w, x, y, z], minterms, dontcares)
    z & (y | ~w)

    They can also be specified using dicts, which does not have to be fully
    specified:

    >>> minterms = [{w: 0, x: 1}, {y: 1, z: 1, x: 0}]
    >>> POSform([w, x, y, z], minterms)
    (x | y) & (x | z) & (~w | ~x)

    Or a combination:

    >>> minterms = [4, 7, 11, [1, 1, 1, 1]]
    >>> dontcares = [{w : 0, x : 0, y: 0}, 5]
    >>> POSform([w, x, y, z], minterms, dontcares)
    (w | x) & (y | ~w) & (z | ~y)


    References
    ==========

    .. [1] en.wikipedia.org/wiki/Quine-McCluskey_algorithm

    """
    variables = [sympify(v) for v in variables]
    if minterms == []:
        return false

    minterms = _input_to_binlist(minterms, variables)
    dontcares = _input_to_binlist((dontcares or []), variables)
    for d in dontcares:
        if d in minterms:
            raise ValueError('%s in minterms is also in dontcares' % d)

    maxterms = []
    for t in product([0, 1], repeat=len(variables)):
        t = list(t)
        if (t not in minterms) and (t not in dontcares):
            maxterms.append(t)
    old = None
    new = maxterms + dontcares
    while new != old:
        old = new
        new = _simplified_pairs(old)
    essential = _rem_redundancy(new, maxterms)
    return And(*[_convert_to_varsPOS(x, variables) for x in essential])


def _find_predicates(expr):
    """Helper to find logical predicates in BooleanFunctions.

    A logical predicate is defined here as anything within a BooleanFunction
    that is not a BooleanFunction itself.

    """
    if not isinstance(expr, BooleanFunction):
        return {expr}
    return set().union(*(_find_predicates(i) for i in expr.args))


def simplify_logic(expr, form=None, deep=True, force=False):
    """
    This function simplifies a boolean function to its simplified version
    in SOP or POS form. The return type is an Or or And object in SymPy.

    Parameters
    ==========

    expr : string or boolean expression

    form : string ('cnf' or 'dnf') or None (default).
        If 'cnf' or 'dnf', the simplest expression in the corresponding
        normal form is returned; if None, the answer is returned
        according to the form with fewest args (in CNF by default).

    deep : boolean (default True)
        Indicates whether to recursively simplify any
        non-boolean functions contained within the input.

    force : boolean (default False)
        As the simplifications require exponential time in the number of
        variables, there is by default a limit on expressions with 8 variables.
        When the expression has more than 8 variables only symbolical
        simplification (controlled by ``deep``) is made. By setting force to ``True``, this limit
        is removed. Be aware that this can lead to very long simplification times.

    Examples
    ========

    >>> from sympy.logic import simplify_logic
    >>> from sympy.abc import x, y, z
    >>> from sympy import S
    >>> b = (~x & ~y & ~z) | ( ~x & ~y & z)
    >>> simplify_logic(b)
    ~x & ~y

    >>> S(b)
    (z & ~x & ~y) | (~x & ~y & ~z)
    >>> simplify_logic(_)
    ~x & ~y

    """

    if form not in (None, 'cnf', 'dnf'):
        raise ValueError("form can be cnf or dnf only")
    expr = sympify(expr)
    if deep:
        variables = _find_predicates(expr)
        from sympy.simplify.simplify import simplify
        s = [simplify(v) for v in variables]
        expr = expr.xreplace(dict(zip(variables, s)))
    if not isinstance(expr, BooleanFunction):
        return expr
    # get variables in case not deep or after doing
    # deep simplification since they may have changed
    variables = _find_predicates(expr)
    if not force and len(variables) > 8:
        return expr
    # group into constants and variable values
    c, v = sift(variables, lambda x: x in (True, False), binary=True)
    variables = c + v
    truthtable = []
    # standardize constants to be 1 or 0 in keeping with truthtable
    c = [1 if i == True else 0 for i in c]
    for t in product([0, 1], repeat=len(v)):
        if expr.xreplace(dict(zip(v, t))) == True:
            truthtable.append(c + list(t))
    big = len(truthtable) >= (2 ** (len(variables) - 1))
    if form == 'dnf' or form is None and big:
        return SOPform(variables, truthtable)
    return POSform(variables, truthtable)


def _finger(eq):
    """
    Assign a 5-item fingerprint to each symbol in the equation:
    [
    # of times it appeared as a Symbol,
    # of times it appeared as a Not(symbol),
    # of times it appeared as a Symbol in an And or Or,
    # of times it appeared as a Not(Symbol) in an And or Or,
    sum of the number of arguments with which it appeared
    as a Symbol, counting Symbol as 1 and Not(Symbol) as 2
    and counting self as 1
    ]

    >>> from sympy.logic.boolalg import _finger as finger
    >>> from sympy import And, Or, Not
    >>> from sympy.abc import a, b, x, y
    >>> eq = Or(And(Not(y), a), And(Not(y), b), And(x, y))
    >>> dict(finger(eq))
    {(0, 0, 1, 0, 2): [x], (0, 0, 1, 0, 3): [a, b], (0, 0, 1, 2, 2): [y]}
    >>> dict(finger(x & ~y))
    {(0, 1, 0, 0, 0): [y], (1, 0, 0, 0, 0): [x]}

    The equation must not have more than one level of nesting:

    >>> dict(finger(And(Or(x, y), y)))
    {(0, 0, 1, 0, 2): [x], (1, 0, 1, 0, 2): [y]}
    >>> dict(finger(And(Or(x, And(a, x)), y)))
    Traceback (most recent call last):
    ...
    NotImplementedError: unexpected level of nesting

    So y and x have unique fingerprints, but a and b do not.
    """
    f = eq.free_symbols
    d = dict(list(zip(f, [[0] * 5 for fi in f])))
    for a in eq.args:
        if a.is_Symbol:
            d[a][0] += 1
        elif a.is_Not:
            d[a.args[0]][1] += 1
        else:
            o = len(a.args) + sum(isinstance(ai, Not) for ai in a.args)
            for ai in a.args:
                if ai.is_Symbol:
                    d[ai][2] += 1
                    d[ai][-1] += o
                elif ai.is_Not:
                    d[ai.args[0]][3] += 1
                else:
                    raise NotImplementedError('unexpected level of nesting')
    inv = defaultdict(list)
    for k, v in ordered(iter(d.items())):
        inv[tuple(v)].append(k)
    return inv


def bool_map(bool1, bool2):
    """
    Return the simplified version of bool1, and the mapping of variables
    that makes the two expressions bool1 and bool2 represent the same
    logical behaviour for some correspondence between the variables
    of each.
    If more than one mappings of this sort exist, one of them
    is returned.
    For example, And(x, y) is logically equivalent to And(a, b) for
    the mapping {x: a, y:b} or {x: b, y:a}.
    If no such mapping exists, return False.

    Examples
    ========

    >>> from sympy import SOPform, bool_map, Or, And, Not, Xor
    >>> from sympy.abc import w, x, y, z, a, b, c, d
    >>> function1 = SOPform([x, z, y],[[1, 0, 1], [0, 0, 1]])
    >>> function2 = SOPform([a, b, c],[[1, 0, 1], [1, 0, 0]])
    >>> bool_map(function1, function2)
    (y & ~z, {y: a, z: b})

    The results are not necessarily unique, but they are canonical. Here,
    ``(w, z)`` could be ``(a, d)`` or ``(d, a)``:

    >>> eq =  Or(And(Not(y), w), And(Not(y), z), And(x, y))
    >>> eq2 = Or(And(Not(c), a), And(Not(c), d), And(b, c))
    >>> bool_map(eq, eq2)
    ((x & y) | (w & ~y) | (z & ~y), {w: a, x: b, y: c, z: d})
    >>> eq = And(Xor(a, b), c, And(c,d))
    >>> bool_map(eq, eq.subs(c, x))
    (c & d & (a | b) & (~a | ~b), {a: a, b: b, c: d, d: x})

    """

    def match(function1, function2):
        """Return the mapping that equates variables between two
        simplified boolean expressions if possible.

        By "simplified" we mean that a function has been denested
        and is either an And (or an Or) whose arguments are either
        symbols (x), negated symbols (Not(x)), or Or (or an And) whose
        arguments are only symbols or negated symbols. For example,
        And(x, Not(y), Or(w, Not(z))).

        Basic.match is not robust enough (see issue 4835) so this is
        a workaround that is valid for simplified boolean expressions
        """

        # do some quick checks
        if function1.__class__ != function2.__class__:
            return None  # maybe simplification makes them the same?
        if len(function1.args) != len(function2.args):
            return None  # maybe simplification makes them the same?
        if function1.is_Symbol:
            return {function1: function2}

        # get the fingerprint dictionaries
        f1 = _finger(function1)
        f2 = _finger(function2)

        # more quick checks
        if len(f1) != len(f2):
            return False

        # assemble the match dictionary if possible
        matchdict = {}
        for k in f1.keys():
            if k not in f2:
                return False
            if len(f1[k]) != len(f2[k]):
                return False
            for i, x in enumerate(f1[k]):
                matchdict[x] = f2[k][i]
        return matchdict

    a = simplify_logic(bool1)
    b = simplify_logic(bool2)
    m = match(a, b)
    if m:
        return a, m
    return m


def simplify_patterns_and():
    from sympy.functions.elementary.miscellaneous import Min, Max
    from sympy.core import Wild
    from sympy.core.relational import Eq, Ne, Ge, Gt, Le, Lt
    a = Wild('a')
    b = Wild('b')
    c = Wild('c')
    # With a better canonical fewer results are required
    _matchers_and = ((And(Eq(a, b), Ge(a, b)), Eq(a, b)),
                     (And(Eq(a, b), Gt(a, b)), S.false),
                     (And(Eq(a, b), Le(a, b)), Eq(a, b)),
                     (And(Eq(a, b), Lt(a, b)), S.false),
                     (And(Ge(a, b), Gt(a, b)), Gt(a, b)),
                     (And(Ge(a, b), Le(a, b)), Eq(a, b)),
                     (And(Ge(a, b), Lt(a, b)), S.false),
                     (And(Ge(a, b), Ne(a, b)), Gt(a, b)),
                     (And(Gt(a, b), Le(a, b)), S.false),
                     (And(Gt(a, b), Lt(a, b)), S.false),
                     (And(Gt(a, b), Ne(a, b)), Gt(a, b)),
                     (And(Le(a, b), Lt(a, b)), Lt(a, b)),
                     (And(Le(a, b), Ne(a, b)), Lt(a, b)),
                     (And(Lt(a, b), Ne(a, b)), Lt(a, b)),
                     # Min/max
                     (And(Ge(a, b), Ge(a, c)), Ge(a, Max(b, c))),
                     (And(Ge(a, b), Gt(a, c)), ITE(b > c, Ge(a, b), Gt(a, c))),
                     (And(Gt(a, b), Gt(a, c)), Gt(a, Max(b, c))),
                     (And(Le(a, b), Le(a, c)), Le(a, Min(b, c))),
                     (And(Le(a, b), Lt(a, c)), ITE(b < c, Le(a, b), Lt(a, c))),
                     (And(Lt(a, b), Lt(a, c)), Lt(a, Min(b, c))),
                     # Sign
                     (And(Eq(a, b), Eq(a, -b)), And(Eq(a, S(0)), Eq(b, S(0)))),
                     )
    return _matchers_and


def simplify_patterns_or():
    from sympy.functions.elementary.miscellaneous import Min, Max
    from sympy.core import Wild
    from sympy.core.relational import Eq, Ne, Ge, Gt, Le, Lt
    a = Wild('a')
    b = Wild('b')
    c = Wild('c')
    _matchers_or = ((Or(Eq(a, b), Ge(a, b)), Ge(a, b)),
                    (Or(Eq(a, b), Gt(a, b)), Ge(a, b)),
                    (Or(Eq(a, b), Le(a, b)), Le(a, b)),
                    (Or(Eq(a, b), Lt(a, b)), Le(a, b)),
                    (Or(Ge(a, b), Gt(a, b)), Ge(a, b)),
                    (Or(Ge(a, b), Le(a, b)), S.true),
                    (Or(Ge(a, b), Lt(a, b)), S.true),
                    (Or(Ge(a, b), Ne(a, b)), S.true),
                    (Or(Gt(a, b), Le(a, b)), S.true),
                    (Or(Gt(a, b), Lt(a, b)), Ne(a, b)),
                    (Or(Gt(a, b), Ne(a, b)), Ne(a, b)),
                    (Or(Le(a, b), Lt(a, b)), Le(a, b)),
                    (Or(Le(a, b), Ne(a, b)), S.true),
                    (Or(Lt(a, b), Ne(a, b)), Ne(a, b)),
                    # Min/max
                    (Or(Ge(a, b), Ge(a, c)), Ge(a, Min(b, c))),
                    (Or(Ge(a, b), Gt(a, c)), ITE(b > c, Gt(a, c), Ge(a, b))),
                    (Or(Gt(a, b), Gt(a, c)), Gt(a, Min(b, c))),
                    (Or(Le(a, b), Le(a, c)), Le(a, Max(b, c))),
                    (Or(Le(a, b), Lt(a, c)), ITE(b >= c, Le(a, b), Lt(a, c))),
                    (Or(Lt(a, b), Lt(a, c)), Lt(a, Max(b, c))),
                    )
    return _matchers_or


def simplify_patterns_xor():
    from sympy.functions.elementary.miscellaneous import Min, Max
    from sympy.core import Wild
    from sympy.core.relational import Eq, Ne, Ge, Gt, Le, Lt
    a = Wild('a')
    b = Wild('b')
    c = Wild('c')
    _matchers_xor = ((Xor(Eq(a, b), Ge(a, b)), Gt(a, b)),
                     (Xor(Eq(a, b), Gt(a, b)), Ge(a, b)),
                     (Xor(Eq(a, b), Le(a, b)), Lt(a, b)),
                     (Xor(Eq(a, b), Lt(a, b)), Le(a, b)),
                     (Xor(Ge(a, b), Gt(a, b)), Eq(a, b)),
                     (Xor(Ge(a, b), Le(a, b)), Ne(a, b)),
                     (Xor(Ge(a, b), Lt(a, b)), S.true),
                     (Xor(Ge(a, b), Ne(a, b)), Le(a, b)),
                     (Xor(Gt(a, b), Le(a, b)), S.true),
                     (Xor(Gt(a, b), Lt(a, b)), Ne(a, b)),
                     (Xor(Gt(a, b), Ne(a, b)), Lt(a, b)),
                     (Xor(Le(a, b), Lt(a, b)), Eq(a, b)),
                     (Xor(Le(a, b), Ne(a, b)), Ge(a, b)),
                     (Xor(Lt(a, b), Ne(a, b)), Gt(a, b)),
                     # Min/max
                     (Xor(Ge(a, b), Ge(a, c)),
                      And(Ge(a, Min(b, c)), Lt(a, Max(b, c)))),
                     (Xor(Ge(a, b), Gt(a, c)),
                      ITE(b > c, And(Gt(a, c), Lt(a, b)),
                          And(Ge(a, b), Le(a, c)))),
                     (Xor(Gt(a, b), Gt(a, c)),
                      And(Gt(a, Min(b, c)), Le(a, Max(b, c)))),
                     (Xor(Le(a, b), Le(a, c)),
                      And(Le(a, Max(b, c)), Gt(a, Min(b, c)))),
                     (Xor(Le(a, b), Lt(a, c)),
                      ITE(b < c, And(Lt(a, c), Gt(a, b)),
                          And(Le(a, b), Ge(a, c)))),
                     (Xor(Lt(a, b), Lt(a, c)),
                      And(Lt(a, Max(b, c)), Ge(a, Min(b, c)))),
                     )
    return _matchers_xor

binary_operators = 'equ', 'Is', 'eq', 'ne', 'gt', 'ge', 'lt', 'le', 'at', 'to', 'subset', 'supset', 'et', 'ou', 'distributed'
def inference_type(tokens):

    for token in ('of', 'given', *binary_operators):
        try:
            return tokens.index(token), token
        except ValueError:
            ...

    if m := re.match('[A-Z][a-z]*', tokens[0]):
        if m[0] in ('Eq', 'Ne', 'Gt', 'Ge', 'Lt', 'Le', 'And', 'Or', 'Element', 'Any', 'All', 'Not', 'Subset', 'Supset', 'Imply', 'Iff', 'Cond', 'Given', 'Distributed', 'Contain'):
            return -1, 'Is'
    return -1, 'Is'


def split_and(module):
    cell_contents = module.apply.__closure__[0].cell_contents
    co_argcount = cell_contents.__code__.co_argcount
    if cell_contents.__defaults__ is not None:
        co_argcount -= len(cell_contents.__defaults__)
    return co_argcount > 1
