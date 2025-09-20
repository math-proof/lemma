from sympy.core import Basic, S, Function, diff, Tuple, Dummy
from sympy.core.basic import as_Basic

from sympy.core.numbers import Rational, NumberSymbol
from sympy.core.relational import Equal, Unequal, Relational, _canonical
from sympy.functions.elementary.miscellaneous import Max, Min
from sympy.logic.boolalg import And, Boolean, distribute_and_over_or, Or, ITE, simplify_logic
from sympy.utilities.iterables import uniq, ordered, product, sift
from sympy.utilities.misc import filldedent, func_name
from sympy.sets.fancysets import Reals
from sympy.core.cache import cacheit

Undefined = S.NaN  # Piecewise()


class ExprCondPair(Basic):
    """Represents an expression, condition pair."""

    def __new__(cls, expr, cond, sympify=True):
        if sympify:
            expr = as_Basic(expr)
        if cond is True:
            cond = S.true
        elif cond is False:
            cond = S.false
        return Tuple.__new__(cls, expr, cond, sympify=False)

    @property
    def expr(self):
        """
        Returns the expression of this pair.
        """
        return self.args[0]

    @property
    def cond(self):
        """
        Returns the condition of this pair.
        """
        return self.args[1]

    def __iter__(self):
        yield self.expr
        yield self.cond

    def _eval_simplify(self, ratio, measure, rational, inverse):
        return self.func(*[a.simplify() for a in self.args])

    def inference_status(self, child):
        assert child == 0, "boolean conditions within ExprCondPair are not applicable for inequivalent inference!"
        return False
    
    def __getitem__(self, i):
        return self.args[i]

    def __len__(self):
        return 2
    
    @cacheit
    def _eval_domain_defined(self, x, **_):
        domain = Basic._eval_domain_defined(self, x)
        for arg in self.args:
            domain &= arg.domain_defined(x)
        return domain

    def limits_in_context(self, has_args=None, parent=None):
        cond = self.cond
        for e, c in parent.args:
            if e == self.expr:
                break
            cond &= c.invert()

        if cond.is_And:
            return [(eq.wrt, eq) for eq in cond.args]
        else: 
            return [(cond.wrt, cond)]

    def _sympystr(self, p):
        return '(%s, %s)' % (p._print(self.expr), p._print(self.cond))

    def _lean(self, p):
        return '(%s, %s)' % (p._print(self.expr), p._print(self.cond))


class Piecewise(Function):
    """
    Represents a piecewise function.

    Usage:

      Piecewise( (expr,cond), (expr,cond), ... )
        - Each argument is a 2-tuple defining an expression and condition
        - The conds are evaluated in turn returning the first that is True.
          If any of the evaluated conds are not determined explicitly False,
          e.g. x < 1, the function is returned in symbolic form.
        - If the function is evaluated at a place where all conditions are False,
          nan will be returned.
        - Pairs where the cond is explicitly False, will be removed.

    Examples
    ========

    >>> from sympy import Piecewise, log, ITE, piecewise_fold
    >>> from sympy.abc import x, y
    >>> f = x**2
    >>> g = log(x)
    >>> p = Piecewise((0, x < -1), (f, x <= 1), (g, True))
    >>> p.subs(x,1)
    1
    >>> p.subs(x,5)
    log(5)

    Booleans can contain Piecewise elements:

    >>> cond = (x < y).subs(x, Piecewise((2, x < 0), (3, True))); cond
    Piecewise((2, x < 0), (3, True)) < y

    The folded version of this results in a Piecewise whose
    expressions are Booleans:

    >>> folded_cond = piecewise_fold(cond); folded_cond
    Piecewise((2 < y, x < 0), (3 < y, True))

    When a Boolean containing Piecewise (like cond) or a Piecewise
    with Boolean expressions (like folded_cond) is used as a condition,
    it is converted to an equivalent ITE object:

    >>> Piecewise((1, folded_cond))
    Piecewise((1, ITE(x < 0, y > 2, y > 3)))

    When a condition is an ITE, it will be converted to a simplified
    Boolean expression:

    >>> piecewise_fold(_)
    Piecewise((1, ((x >= 0) | (y > 2)) & ((y > 3) | (x < 0))))

    See Also
    ========
    piecewise_fold, ITE
    """

    nargs = None

    @property
    def scope_variables(self):
        s = None
        for _, c in self.args[:-1]:
            if c.is_Element: 
                free_symbols = c.lhs.free_symbols
            else:
                free_symbols = c.free_symbols
            if s is None:
                s = free_symbols
            else:
                s = s & free_symbols
        return s
        
    @property
    def set(self):
        newargs = []
        for e, c in self.args:
            newargs.append((e.set, c))
        return self.func(*newargs, evaluate=False)

    @property
    def is_set(self):
        for e, _ in self.args:
            return e.is_set

    def __new__(cls, *args, **options):
        if len(args) == 0:
            raise TypeError("At least one (expr, cond) pair expected.")
        # (Try to) sympify args first
        newargs = []
        sympify = options.pop('sympify', True)
        for ec in args:
            # ec could be a ExprCondPair or a tuple
            pair = ExprCondPair(*getattr(ec, 'args', ec), sympify=sympify)
            cond = pair.cond
            if cond.is_BooleanFalse:
                continue
            newargs.append(pair)
            if cond == True:
                break
            
        if options.pop('evaluate', True):
            r = cls.eval(*newargs)
        else:
            r = None

        if r is None:
            return Basic.__new__(cls, *newargs, **options)
        else:
            return r

    @cacheit
    def _eval_shape(self):
        for e, _ in self.args:
            return e.shape

    @classmethod
    def eval(cls, *_args):
        """Either return a modified version of the args or, if no
        modifications were made, return None.

        Modifications that are made here:
        1) relationals are made canonical
        2) any False conditions are dropped
        3) any repeat of a previous condition is ignored
        3) any args past one with a true condition are dropped

        If there are no args left, nan will be returned.
        If there is a single arg with a True condition, its
        corresponding expression will be returned.
        """

        if not _args:
            return Undefined

        if len(_args) == 1 and _args[0][-1] == True:
            return _args[0][0]

        newargs = []  # the unevaluated conditions
        current_cond = set()  # the conditions up to a given e, c pair
        # make conditions canonical
        args = []
        for e, c in _args:
            if not c.is_Atom and not isinstance(c, Relational):
                free = c.free_symbols
                if len(free) == 1:
                    funcs = [i for i in c.atoms(Function) if not isinstance(i, Boolean)]
                    if len(funcs) == 1 and len(c.xreplace({list(funcs)[0]: Dummy()}).free_symbols) == 1:
                        # we can treat function like a symbol
                        free = funcs
                    _c = c
                    x, = free
                    try:
                        c = c.as_set().as_relational(x)
                    except:
                        pass
                    else:
                        reps = {}
                        for i in c.atoms(Relational):
                            ic = i.canonical
                            if ic.rhs in (S.Infinity, S.NegativeInfinity):
                                if not _c.has(ic.rhs):
                                    # don't accept introduction of
                                    # new Relationals with +/-oo
                                    reps[i] = S.true
                                elif ('=' not in ic.rel_op and c.xreplace({x: i.rhs}) != _c.xreplace({x: i.rhs})):
                                    reps[i] = Relational(i.lhs, i.rhs, i.rel_op + '=')
                        c = c.xreplace(reps)
            args.append((e, c))
#             args.append((e, _canonical(c)))

        for expr, cond in args:
            # Check here if expr is a Piecewise and collapse if one of
            # the conds in expr matches cond. This allows the collapsing
            # of Piecewise((Piecewise((x,x<0)),x<0)) to Piecewise((x,x<0)).
            # This is important when using piecewise_fold to simplify
            # multiple Piecewise instances having the same conds.
            # Eventually, this code should be able to collapse Piecewise's
            # having different intervals, but this will probably require
            # using the new assumptions.
            if isinstance(expr, Piecewise):
                unmatching = []
                for i, (e, c) in enumerate(expr.args):
                    if c in current_cond:
                        # this would already have triggered
                        continue
                    if c == cond:
                        if c != True:
                            # nothing past this condition will ever
                            # trigger and only those args before this
                            # that didn't match a previous condition
                            # could possibly trigger
                            if unmatching:
                                expr = Piecewise(*unmatching, (e, True))
                            else:
                                expr = e
                        break
                    else:
                        unmatching.append((e, c))

            # check for condition repeats
            got = False
            # -- if an And contains a condition that was
            #    already encountered, then the And will be
            #    False: if the previous condition was False
            #    then the And will be False and if the previous
            #    condition is True then then we wouldn't get to
            #    this point. In either case, we can skip this condition.
            for i in ([cond] + (list(cond.args) if isinstance(cond, And) else [])):
                if i in current_cond:
                    got = True
                    break
            if got:
                continue

            # -- if not(c) is already in current_cond then c is
            #    a redundant condition in an And. This does not
            #    apply to Or, however: (e1, c), (e2, Or(~c, d))
            #    is not (e1, c), (e2, d) because if c and d are
            #    both False this would give no results when the
            #    true answer should be (e2, True)
            if isinstance(cond, And):
                nonredundant = []
                for c in cond.args:
                    if (isinstance(c, Relational) and c.invert().canonical in current_cond):
                        continue
                    nonredundant.append(c)
                cond = cond.func(*nonredundant)
            elif isinstance(cond, Relational):
                if current_cond and cond.invert().canonical in current_cond:
                    cond = S.true

            current_cond.add(cond)

            # collect successive e,c pairs when exprs or cond match
            if newargs:
                if newargs[-1].expr == expr:
                    orcond = cond | newargs[-1].cond
                    if isinstance(orcond, (And, Or)):
                        orcond = distribute_and_over_or(orcond).simplify()
                    newargs[-1] = ExprCondPair(expr, orcond)
                    continue
                elif newargs[-1].cond == cond:
                    orexpr = Or(expr, newargs[-1].expr)
                    if isinstance(orexpr, (And, Or)):
                        orexpr = distribute_and_over_or(orexpr).simplify()
                    newargs[-1] = ExprCondPair(orexpr, cond)
                    continue

            newargs.append(ExprCondPair(expr, cond))

        # some conditions may have been redundant
        missing = len(newargs) != len(_args)
        # some conditions may have changed
        same = all(a == b for a, b in zip(newargs, _args))
        # if either change happened we return the expr with the
        # updated args
        if not newargs:
            raise ValueError(filldedent('''
                There are no conditions (or none that
                are not trivially false) to define an
                expression.'''))
        if missing or not same:
            return cls(*newargs)

    def doit(self, **hints):
        """
        Evaluate this piecewise function.
        """
        newargs = []
        for e, c in self.args:
            if hints.get('deep', True):
                if isinstance(e, Basic):
                    e = e.doit(**hints)
                if isinstance(c, Basic):
                    c = c.doit(**hints)
            newargs.append((e, c))
        return self.func(*newargs)

    def __sub__(self, other):
        if isinstance(other, Basic):
            if other.is_Piecewise: 
                other = self.func(*((-e, c) for e, c in other.args))
                return Function.__add__(self, other)
            
            if other.is_Function:
                return Function.__sub__(self, other)
        
        newargs = []
        for e, c in self.args:
            newargs.append((e - other, c))
        return self.func(*newargs)

    def _eval_simplify(self, ratio, measure, rational, inverse):
        args = [a._eval_simplify(ratio, measure, rational, inverse)
            for a in self.args]
        _blessed = lambda e: getattr(e.lhs, '_diff_wrt', False) and (
            getattr(e.rhs, '_diff_wrt', None) or
            isinstance(e.rhs, (Rational, NumberSymbol)))
        for i, (expr, cond) in enumerate(args):
            # try to simplify conditions and the expression for
            # equalities that are part of the condition, e.g.
            # Piecewise((n, And(Eq(n,0), Eq(n + m, 0))), (1, True))
            # -> Piecewise((0, And(Eq(n, 0), Eq(m, 0))), (1, True))
            if isinstance(cond, And):
                eqs, other = sift(cond.args,
                    lambda i: isinstance(i, Equal), binary=True)
            elif isinstance(cond, Equal):
                eqs, other = [cond], []
            else:
                eqs = other = []
            if eqs:
                eqs = list(ordered(eqs))
                for j, e in enumerate(eqs):
                    # these blessed lhs objects behave like Symbols
                    # and the rhs are simple replacements for the "symbols"
                    if _blessed(e):
                        expr = expr.subs(*e.args)
                        eqs[j + 1:] = [ei.subs(*e.args) for ei in eqs[j + 1:]]
                        other = [ei.subs(*e.args) for ei in other]
                cond = And(*(eqs + other))
                args[i] = args[i].func(expr, cond)
        # See if expressions valid for an Equal expression happens to evaluate
        # to the same function as in the next piecewise segment, see:
        # https://github.com/sympy/sympy/issues/8458
        prevexpr = None
        for i, (expr, cond) in reversed(list(enumerate(args))):
            if prevexpr is not None:
                if isinstance(cond, And):
                    eqs, other = sift(cond.args,
                        lambda i: isinstance(i, Equal), binary=True)
                elif isinstance(cond, Equal):
                    eqs, other = [cond], []
                else:
                    eqs = other = []
                _prevexpr = prevexpr
                _expr = expr
                if eqs and not other:
                    eqs = list(ordered(eqs))
                    for e in eqs:
                        # these blessed lhs objects behave like Symbols
                        # and the rhs are simple replacements for the "symbols"
                        if _blessed(e):
                            _prevexpr = _prevexpr.subs(*e.args)
                            _expr = _expr.subs(*e.args)
                # Did it evaluate to the same?
                if _prevexpr == _expr:
                    # Set the expression for the Not equal section to the same
                    # as the next. These will be merged when creating the new
                    # Piecewise
                    args[i] = args[i].func(args[i + 1][0], cond)
                else:
                    # Update the expression that we compare against
                    prevexpr = expr
            else:
                prevexpr = expr
        return self.func(*args)

    def _eval_as_leading_term(self, x):
        for e, c in self.args:
            if c == True or c.subs(x, 0) == True:
                return e.as_leading_term(x)

    def _eval_adjoint(self):
        return self.func(*[(e.adjoint(), c) for e, c in self.args])

    def _eval_conjugate(self):
        return self.func(*[(e.conjugate(), c) for e, c in self.args])

    def _eval_derivative(self, x):
        return self.func(*[(diff(e, x), c) for e, c in self.args])

    def _eval_evalf(self, prec):
        return self.func(*[(e._evalf(prec), c) for e, c in self.args])

    def piecewise_integrate(self, x, **kwargs):
        """Return the Piecewise with each expression being
        replaced with its antiderivative. To obtain a continuous
        antiderivative, use the `integrate` function or method.

        Examples
        ========

        >>> from sympy import Piecewise
        >>> from sympy.abc import x
        >>> p = Piecewise((0, x < 0), (1, x < 1), (2, True))
        >>> p.piecewise_integrate(x)
        Piecewise((0, x < 0), (x, x < 1), (2*x, True))

        Note that this does not give a continuous function, e.g.
        at x = 1 the 3rd condition applies and the antiderivative
        there is 2*x so the value of the antiderivative is 2:

        >>> anti = _
        >>> anti.subs(x, 1)
        2

        The continuous derivative accounts for the integral *up to*
        the point of interest, however:

        >>> p.integrate(x)
        Piecewise((0, x < 0), (x, x < 1), (2*x - 1, True))
        >>> _.subs(x, 1)
        1

        See Also
        ========
        Piecewise._eval_integral
        """
        from sympy.integrals import integrate
        return self.func(*[(integrate(e, x, **kwargs), c) for e, c in self.args])

    def _handle_irel(self, x, handler):
        """Return either None (if the conditions of self depend only on x) else
        a Piecewise expression whose expressions (handled by the handler that
        was passed) are paired with the governing x-independent relationals,
        e.g. Piecewise((A, a(x) & b(y)), (B, c(x) | c(y)) ->
        Piecewise(
            (handler(Piecewise((A, a(x) & True), (B, c(x) | True)), b(y) & c(y)),
            (handler(Piecewise((A, a(x) & True), (B, c(x) | False)), b(y)),
            (handler(Piecewise((A, a(x) & False), (B, c(x) | True)), c(y)),
            (handler(Piecewise((A, a(x) & False), (B, c(x) | False)), True))
        """
        # identify governing relationals
        rel = self.atoms(Relational)
        irel = list(ordered([r for r in rel if x not in r.free_symbols
            and r not in (S.true, S.false)]))
        if irel:
            args = {}
            exprinorder = []
            for truth in product((1, 0), repeat=len(irel)):
                reps = dict(zip(irel, truth))
                # only store the true conditions since the false are implied
                # when they appear lower in the Piecewise args
                if 1 not in truth:
                    cond = None  # flag this one so it doesn't get combined
                else:
                    andargs = Tuple(*[i for i in reps if reps[i]])
                    free = list(andargs.free_symbols)
                    if len(free) == 1:
                        from sympy.solvers.inequalities import (
                            reduce_inequalities, _solve_inequality)
                        try:
                            t = reduce_inequalities(andargs, free[0])
                            # ValueError when there are potentially
                            # nonvanishing imaginary parts
                        except (ValueError, NotImplementedError):
                            # at least isolate free symbol on left
                            t = And(*[_solve_inequality(
                                a, free[0], linear=True)
                                for a in andargs])
                    else:
                        t = And(*andargs)
                    if t is S.false:
                        continue  # an impossible combination
                    cond = t
                expr = handler(self.xreplace(reps))
                if isinstance(expr, self.func) and len(expr.args) == 1:
                    expr, econd = expr.args[0]
                    cond = And(econd, True if cond is None else cond)
                # the ec pairs are being collected since all possibilities
                # are being enumerated, but don't put the last one in since
                # its expr might match a previous expression and it
                # must appear last in the args
                if cond is not None:
                    args.setdefault(expr, []).append(cond)
                    # but since we only store the true conditions we must maintain
                    # the order so that the expression with the most true values
                    # comes first
                    exprinorder.append(expr)
            # convert collected conditions as args of Or
            for k in args:
                args[k] = Or(*args[k])
            # take them in the order obtained
            args = [(e, args[e]) for e in uniq(exprinorder)]
            # add in the last arg
            args.append((expr, True))
            # if any condition reduced to True, it needs to go last
            # and there should only be one of them or else the exprs
            # should agree
            trues = [i for i in range(len(args)) if args[i][1] is S.true]
            if not trues:
                # make the last one True since all cases were enumerated
                e, c = args[-1]
                args[-1] = (e, S.true)
            else:
                assert len(set([e for e, c in [args[i] for i in trues]])) == 1
                args.append(args.pop(trues.pop()))
                while trues:
                    args.pop(trues.pop())
            return Piecewise(*args)

    def _eval_integral(self, x, _first=True, **kwargs):
        """Return the indefinite integral of the
        Piecewise such that subsequent substitution of x with a
        value will give the value of the integral (not including
        the constant of integration) up to that point. To only
        integrate the individual parts of Piecewise, use the
        `piecewise_integrate` method.

        Examples
        ========

        >>> from sympy import Piecewise
        >>> from sympy.abc import x
        >>> p = Piecewise((0, x < 0), (1, x < 1), (2, True))
        >>> p.integrate(x)
        Piecewise((0, x < 0), (x, x < 1), (2*x - 1, True))
        >>> p.piecewise_integrate(x)
        Piecewise((0, x < 0), (x, x < 1), (2*x, True))

        See Also
        ========
        Piecewise.piecewise_integrate
        """
        from sympy.integrals.integrals import integrate

        if _first:

            def handler(ipw):
                if isinstance(ipw, self.func):
                    return ipw._eval_integral(x, _first=False, **kwargs)
                else:
                    return ipw.integrate(x, **kwargs)

            irv = self._handle_irel(x, handler)
            if irv is not None:
                return irv

        # handle a Piecewise from -oo to oo with and no x-independent relationals
        # -----------------------------------------------------------------------
        try:
            abei = self._intervals(x)
        except NotImplementedError:
            from sympy import Integral
            return Integral(self, x)  # unevaluated

        pieces = [(a, b) for a, b, _, _ in abei]
        oo = S.Infinity
        done = [(-oo, oo, -1)]
        for k, p in enumerate(pieces):
            if p == (-oo, oo):
                # all undone intervals will get this key
                for j, (a, b, i) in enumerate(done):
                    if i == -1:
                        done[j] = a, b, k
                break  # nothing else to consider
            N = len(done) - 1
            for j, (a, b, i) in enumerate(reversed(done)):
                if i == -1:
                    j = N - j
                    done[j: j + 1] = _clip(p, (a, b), k)
        done = [(a, b, i) for a, b, i in done if a != b]

        # append an arg if there is a hole so a reference to
        # argument -1 will give Undefined
        if any(i == -1 for (a, b, i) in done):
            abei.append((-oo, oo, Undefined, -1))

        # return the sum of the intervals
        args = []
        sum = None
        for a, b, i in done:
            anti = integrate(abei[i][-2], x, **kwargs)
            if sum is None:
                sum = anti
            else:
                sum = sum.subs(x, a)
                if sum == Undefined:
                    sum = 0
                sum += anti._eval_interval(x, a, x)
            # see if we know whether b is contained in original
            # condition
            if b is S.Infinity:
                cond = True
            elif self.args[abei[i][-1]].cond.subs(x, b) == False:
                cond = (x < b)
            else:
                cond = (x <= b)
            args.append((sum, cond))
        return Piecewise(*args)

    def _eval_interval(self, sym, a, b, _first=True):
        """Evaluates the function along the sym in a given interval [a, b]"""
        # FIXME: Currently complex intervals are not supported.  A possible
        # replacement algorithm, discussed in issue 5227, can be found in the
        # following papers;
        #     http://portal.acm.org/citation.cfm?id=281649
        #     http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.70.4127&rep=rep1&type=pdf
        from sympy.core.symbol import Dummy

        if a is None or b is None:
            # In this case, it is just simple substitution
            return super(Piecewise, self)._eval_interval(sym, a, b)
        else:
            x, lo, hi = map(as_Basic, (sym, a, b))

        if _first:  # get only x-dependent relationals

            def handler(ipw):
                if isinstance(ipw, self.func):
                    return ipw._eval_interval(x, lo, hi, _first=None)
                else:
                    return ipw._eval_interval(x, lo, hi)

            irv = self._handle_irel(x, handler)
            if irv is not None:
                return irv

            if (lo < hi) is S.false or (
                    lo is S.Infinity or hi is S.NegativeInfinity):
                rv = self._eval_interval(x, hi, lo, _first=False)
                if isinstance(rv, Piecewise):
                    rv = Piecewise(*[(-e, c) for e, c in rv.args])
                else:
                    rv = -rv
                return rv

            if (lo < hi) is S.true or (
                    hi is S.Infinity or lo is S.NegativeInfinity):
                pass
            else:
                _a = Dummy('lo')
                _b = Dummy('hi')
                a = lo if lo.is_comparable else _a
                b = hi if hi.is_comparable else _b
                pos = self._eval_interval(x, a, b, _first=False)
                if a == _a and b == _b:
                    # it's purely symbolic so just swap lo and hi and
                    # change the sign to get the value for when lo > hi
                    neg, pos = (-pos.xreplace({_a: hi, _b: lo}),
                        pos.xreplace({_a: lo, _b: hi}))
                else:
                    # at least one of the bounds was comparable, so allow
                    # _eval_interval to use that information when computing
                    # the interval with lo and hi reversed
                    neg, pos = (-self._eval_interval(x, hi, lo, _first=False),
                        pos.xreplace({_a: lo, _b: hi}))

                # allow simplification based on ordering of lo and hi
                p = Dummy('', positive=True)
                if lo.is_Symbol:
                    pos = pos.xreplace({lo: hi - p}).xreplace({p: hi - lo})
                    neg = neg.xreplace({lo: hi + p}).xreplace({p: lo - hi})
                elif hi.is_Symbol:
                    pos = pos.xreplace({hi: lo + p}).xreplace({p: hi - lo})
                    neg = neg.xreplace({hi: lo - p}).xreplace({p: lo - hi})

                # assemble return expression; make the first condition be Lt
                # b/c then the first expression will look the same whether
                # the lo or hi limit is symbolic
                if a == _a:  # the lower limit was symbolic
                    rv = Piecewise(
                        (pos,
                            lo < hi),
                        (neg,
                            True))
                else:
                    rv = Piecewise(
                        (neg,
                            hi < lo),
                        (pos,
                            True))

                if rv == Undefined:
                    raise ValueError("Can't integrate across undefined region.")
                if any(isinstance(i, Piecewise) for i in (pos, neg)):
                    rv = piecewise_fold(rv)
                return rv

        # handle a Piecewise with lo <= hi and no x-independent relationals
        # -----------------------------------------------------------------
        try:
            abei = self._intervals(x)
        except NotImplementedError:
            from sympy import Integral
            # not being able to do the interval of f(x) can
            # be stated as not being able to do the integral
            # of f'(x) over the same range
            return Integral(self.diff(x), (x, lo, hi))  # unevaluated

        pieces = [(a, b) for a, b, _, _ in abei]
        done = [(lo, hi, -1)]
        oo = S.Infinity
        for k, p in enumerate(pieces):
            if p[:2] == (-oo, oo):
                # all undone intervals will get this key
                for j, (a, b, i) in enumerate(done):
                    if i == -1:
                        done[j] = a, b, k
                break  # nothing else to consider
            N = len(done) - 1
            for j, (a, b, i) in enumerate(reversed(done)):
                if i == -1:
                    j = N - j
                    done[j: j + 1] = _clip(p, (a, b), k)
        done = [(a, b, i) for a, b, i in done if a != b]

        # return the sum of the intervals
        sum = S.Zero
        upto = None
        for a, b, i in done:
            if i == -1:
                if upto is None:
                    return Undefined
                # TODO simplify hi <= upto
                return Piecewise((sum, hi <= upto), (Undefined, True))
            sum += abei[i][-2]._eval_interval(x, a, b)
            upto = b
        return sum

    def _intervals(self, sym):
        """Return a list of unique tuples, (a, b, e, i), where a and b
        are the lower and upper bounds in which the expression e of
        argument i in self is defined and a < b (when involving
        numbers) or a <= b when involving symbols.

        If there are any relationals not involving sym, or any
        relational cannot be solved for sym, NotImplementedError is
        raised. The calling routine should have removed such
        relationals before calling this routine.

        The evaluated conditions will be returned as ranges.
        Discontinuous ranges will be returned separately with
        identical expressions. The first condition that evaluates to
        True will be returned as the last tuple with a, b = -oo, oo.
        """
        from sympy.solvers.inequalities import _solve_inequality
        from sympy.logic.boolalg import to_cnf, distribute_or_over_and

        assert isinstance(self, Piecewise)

        def _solve_relational(r):
            if sym not in r.free_symbols:
                nonsymfail(r)
            rv = _solve_inequality(r, sym)
            if isinstance(rv, Relational):
                free = rv.args[1].free_symbols
                if rv.args[0] != sym or sym in free:
                    raise NotImplementedError(filldedent('''
                        Unable to solve relational
                        %s for %s.''' % (r, sym)))
                if rv.rel_op == '==':
                    # this equality has been affirmed to have the form
                    # Eq(sym, rhs) where rhs is sym-free; it represents
                    # a zero-width interval which will be ignored
                    # whether it is an isolated condition or contained
                    # within an And or an Or
                    rv = S.false
                elif rv.rel_op == '!=':
                    try:
                        rv = Or(sym < rv.rhs, sym > rv.rhs)
                    except TypeError:
                        # e.g. x != I ==> all real x satisfy
                        rv = S.true
            elif rv == (S.NegativeInfinity < sym) & (sym < S.Infinity):
                rv = S.true
            return rv

        def nonsymfail(cond):
            raise NotImplementedError(filldedent('''
                A condition not involving
                %s appeared: %s''' % (sym, cond)))

        # make self canonical wrt Relationals
        reps = dict([
            (r, _solve_relational(r)) for r in self.atoms(Relational)])
        # process args individually so if any evaluate, their position
        # in the original Piecewise will be known
        args = [i.xreplace(reps) for i in self.args]

        # precondition args
        expr_cond = []
        default = idefault = None
        for i, (expr, cond) in enumerate(args):
            if cond is S.false:
                continue
            elif cond is S.true:
                default = expr
                idefault = i
                break

            cond = to_cnf(cond)
            if isinstance(cond, And):
                cond = distribute_or_over_and(cond)

            if isinstance(cond, Or):
                expr_cond.extend(
                    [(i, expr, o) for o in cond.args
                    if not isinstance(o, Equal)])
            elif cond is not S.false:
                expr_cond.append((i, expr, cond))

        # determine intervals represented by conditions
        int_expr = []
        for iarg, expr, cond in expr_cond:
            if isinstance(cond, And):
                lower = S.NegativeInfinity
                upper = S.Infinity
                for cond2 in cond.args:
                    if isinstance(cond2, Equal):
                        lower = upper  # ignore
                        break
                    elif cond2.lts == sym:
                        upper = Min(cond2.gts, upper)
                    elif cond2.gts == sym:
                        lower = Max(cond2.lts, lower)
                    else:
                        nonsymfail(cond2)  # should never get here
            elif isinstance(cond, Relational):
                lower, upper = cond.lts, cond.gts  # part 1: initialize with givens
                if cond.lts == sym:  # part 1a: expand the side ...
                    lower = S.NegativeInfinity  # e.g. x <= 0 ---> -oo <= 0
                elif cond.gts == sym:  # part 1a: ... that can be expanded
                    upper = S.Infinity  # e.g. x >= 0 --->  oo >= 0
                else:
                    nonsymfail(cond)
            else:
                raise NotImplementedError(
                    'unrecognized condition: %s' % cond)

            lower, upper = lower, Max(lower, upper)
            if (lower >= upper) is not S.true:
                int_expr.append((lower, upper, expr, iarg))

        if default is not None:
            int_expr.append(
                (S.NegativeInfinity, S.Infinity, default, idefault))

        return list(uniq(int_expr))

    def _eval_nseries(self, x, n, logx):
        args = [(ec.expr._eval_nseries(x, n, logx), ec.cond) for ec in self.args]
        return self.func(*args)

    def _eval_Abs(self):
        args = [(abs(ec.expr), ec.cond) for ec in self.args]
        return self.func(*args)

    def _eval_Card(self):
        from sympy import Card
        args = [(Card(ec.expr), ec.cond) for ec in self.args]
        return self.func(*args)
    
    def _eval_power(self, s):
        return self.func(*[(e ** s, c) for e, c in self.args])

    def _subs(self, old, new, **hints):
        if self == old:
            return new
        # this is strictly not necessary, but we can keep track
        # of whether True or False conditions arise and be
        # somewhat more efficient by avoiding other substitutions
        # and avoiding invalid conditions that appear after a
        # True condition
        args = []
        hit = False
        from sympy.core.basic import _aresame
        
        for e, c in self.args:
            # l in (j; i], old = l in [0; n), new = l in [0; j)∪(i; n)
            _c = c._subs(old, new)
            if _c.is_BooleanFalse:
                hit = True
                continue
            if not _aresame(_c, c):
                hit = True
                c = _c
                      
            _e = e._subs(old, new)
            if not _aresame(_e, e):
                hit = True
                e = _e
                     
            args.append((e, c))
            if c:
                break
        if hit:
            return self.func(*args)
        return self

    def _eval_transpose(self, *axis):
        if axis == self.default_axis:
            return self.func(*((e.T, c) for e, c in self.args))

    def _eval_template_is_attr(self, is_attr):
        b = None
        for expr, _ in self.args:
            a = getattr(expr, is_attr)
            if a is None:
                return
            if b is None:
                b = a
            elif b != a:
                return
        return b

    _eval_is_finite = lambda self: self._eval_template_is_attr('is_finite')
    _eval_is_extended_complex = lambda self: self._eval_template_is_attr('is_extended_complex')
    _eval_is_even = lambda self: self._eval_template_is_attr('is_even')
    _eval_is_imaginary = lambda self: self._eval_template_is_attr('is_imaginary')
    _eval_is_extended_integer = lambda self: self._eval_template_is_attr('is_extended_integer')
    _eval_is_irrational = lambda self: self._eval_template_is_attr('is_irrational')
    _eval_is_negative = lambda self: self._eval_template_is_attr('is_negative')
    _eval_is_polar = lambda self: self._eval_template_is_attr('is_polar')
    _eval_is_positive = lambda self: self._eval_template_is_attr('is_positive')
    _eval_is_extended_real = lambda self: self._eval_template_is_attr('is_extended_real')
    _eval_is_extended_positive = lambda self: self._eval_template_is_attr('is_extended_positive')
    _eval_is_extended_negative = lambda self: self._eval_template_is_attr('is_extended_negative')
    _eval_is_extended_real = lambda self: self._eval_template_is_attr('is_extended_real')
    _eval_is_zero = lambda self: self._eval_template_is_attr('is_zero')

    @classmethod
    def __eval_cond(cls, cond):
        """Return the truth value of the condition."""
        if cond == True:
            return True
        if isinstance(cond, Equal):
            try:
                diff = cond.lhs - cond.rhs
                if diff.is_commutative:
                    return diff.is_zero
            except TypeError:
                pass

    def as_expr_set_pairs(self, domain=Reals):
        """Return tuples for each argument of self that give
        the expression and the interval in which it is valid
        which is contained within the given domain.
        If a condition cannot be converted to a set, an error
        will be raised. The variable of the conditions is
        assumed to be real; sets of real values are returned.

        Examples
        ========

        >>> from sympy import Piecewise, Interval
        >>> from sympy.abc import x
        >>> p = Piecewise(
        ...     (1, x < 2),
        ...     (2,(x > 0) & (x < 4)),
        ...     (3, True))
        >>> p.as_expr_set_pairs()
        [(1, Interval.open(-oo, 2)),
         (2, Interval.Ropen(2, 4)),
         (3, Interval(4, oo))]
        >>> p.as_expr_set_pairs(Interval(0, 3))
        [(1, Interval.Ropen(0, 2)),
         (2, Interval(2, 3)), (3, EmptySet())]
        """
        exp_sets = []
        U = domain
        complex = not domain.is_subset(Reals)
        for expr, cond in self.args:
            if complex:
                for i in cond.atoms(Relational):
                    if not isinstance(i, (Equal, Unequal)):
                        raise ValueError(filldedent('''
                            Inequalities in the complex domain are
                            not supported. Try the real domain by
                            setting domain=Reals'''))
            cond_int = U.intersect(cond.as_set())
            U = U - cond_int
            exp_sets.append((expr, cond_int))
        return exp_sets

    def _eval_rewrite_as_ITE(self, *args, **kwargs):
        byfree = {}
        args = list(args)
        default = any(c == True for b, c in args)
        for i, (b, c) in enumerate(args):
            if not isinstance(b, Boolean) and b != True:
                raise TypeError(filldedent('''
                    Expecting Boolean or bool but got `%s`
                    ''' % func_name(b)))
            if c == True:
                break
            # loop over independent conditions for this b
            for c in c.args if isinstance(c, Or) else [c]:
                free = c.free_symbols
                x = next(iter(free))
                try:
                    byfree[x] = byfree.setdefault(x, x.emptySet).union(c.as_set())
                except NotImplementedError:
                    if not default:
                        raise NotImplementedError(filldedent('''
                            A method to determine whether a multivariate
                            conditional is consistent with a complete coverage
                            of all variables has not been implemented so the
                            rewrite is being stopped after encountering `%s`.
                            This error would not occur if a default expression
                            like `(foo, True)` were given.
                            ''' % c))
                if byfree[x].is_UniversalSet or byfree[x] == Reals:
                    # collapse the ith condition to True and break
                    args[i] = list(args[i])
                    c = args[i][1] = True
                    break
            if c == True:
                break
        if c != True:
            raise ValueError(filldedent('''
                Conditions must cover all reals or a final default
                condition `(foo, True)` must be given.
                '''))
        last, _ = args[i]  # ignore all past ith arg
        for a, c in reversed(args[:i]):
            last = ITE(c, a, last)
        return _canonical(last)

    def domain_nonzero(self, x):
        from sympy.sets.sets import Union
        domain = []
        for function, condition in self.args:
            domain.append(x.domain_conditioned(condition) & function.domain_nonzero(x))
        return Union(*domain)

    @cacheit
    def _eval_domain_defined(self, x, **_):
        domain = x.emptySet
        for expr, cond in self.args:
            domain |= expr.domain_defined(x) & cond.domain_defined(x) & cond.domain_conditioned(x)
        return domain

    @property
    def dtype(self):
        dtype = None
        for expr, _ in self.args:
            _dtype = expr.dtype
            if _dtype is None:
                continue
            if dtype is None or dtype in _dtype and dtype != _dtype:
                dtype = _dtype
        return dtype

    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a Basic object!
        """
        if len(lhs.args) == 2:
            (e0, c0), (e1, _) = lhs.args
            if e0 == rhs:
                if Equal(e1, rhs) == False:
                    return c0
            elif e1 == rhs:
                if Equal(e0, rhs) == False:
                    c1 = c0.invert()
                    return c1
                
        elif rhs.is_Add and lhs in rhs.args:
            cls = rhs.func
            args = [*rhs.args]
            args.remove(lhs)
            return self.func(0, cls(*args)).simplify()
                 
    @classmethod
    def simplify_Unequal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a Basic object!
        """
        if len(lhs.args) == 2:
            (e0, c0), (e1, _) = lhs.args
            if e0 == rhs:
                if Equal(e1, rhs) == False:
                    c1 = c0.invert()
                    return c1
            elif e1 == rhs:
                if Equal(e0, rhs) == False:
                    return c0
                
        elif rhs.is_Add and lhs in rhs.args:
            cls = rhs.func
            args = [*rhs.args]
            args.remove(lhs)
            return self.func(0, cls(*args)).simplify()
        
    @staticmethod
    def simplify_Equality(e0, e1, lhs, rhs):
        from sympy.functions.special.tensor_functions import KroneckerDelta
        hit = False
        if lhs.is_integer and rhs.is_integer:
            eq = KroneckerDelta(lhs, rhs)
            _e1 = e1._subs(eq, S.Zero)
            hit = _e1 != e1
            e1 = _e1
            
            _e0 = e0._subs(eq, S.One)
            hit |= _e0 != e0
            e0 = _e0

        _e0 = e0._subs(lhs, rhs)
        __e0 = e0._subs(rhs, lhs)

        if {e1, e1._subs(lhs, rhs), e1._subs(rhs, lhs)} & {e0, _e0, __e0}:
            return e1
        
        if not e0.is_set and lhs.is_integer and rhs.is_integer:
            e_diff = e0 - e1
            if lhs.is_symbol: 
#                 precautious usage of domain_defined
                domain_defined = e_diff.domain_defined(lhs)
                from sympy import Element
                if Element(rhs, domain_defined) == False:
                    return
                
            delta = KroneckerDelta(lhs, rhs)
            if not lhs.is_Number:
                if e_diff.is_infinite:
                    return
                _e_diff = e_diff._subs(lhs, rhs)
                hit |= _e_diff != e_diff
                delta *= _e_diff

            delta += e1
            _delta = delta.simplify()
            hit |= _delta != delta
            if hit:
                return _delta
            return

        from sympy import Complement
        
        if e1.is_Complement:
            _A, B = e1.args
            if _e0 == e0:
                has_lhs, has_rhs = B._has(lhs), B._has(rhs)
                if has_lhs and not has_rhs:
                    return Complement(e0, Complement(B, B._subs(lhs, rhs)))
                if not has_lhs and has_rhs:
                    return Complement(e0 - Complement(B, B._subs(rhs, lhs)))
                
        if e0.is_EmptySet:
            has_lhs, has_rhs = e1._has(lhs), e1._has(rhs)
            if not has_lhs and has_rhs:
                return Complement(e1, e1._subs(rhs, lhs))
            if has_lhs and not has_rhs:
                return Complement(e1, e1._subs(lhs, rhs))
            
        hit = False
        if len(_e0.free_symbols) < len(e0.free_symbols):
            e0 = _e0
            hit = True
        elif len(__e0.free_symbols) < len(e0.free_symbols):
            e0 = __e0
            hit = True
            
        if e1.is_EmptySet and e0 in {lhs.set, rhs.set}:
            return lhs.set & rhs.set
        
        if hit:
            return Piecewise((e0, Equal(lhs, rhs)), (e1, True))
        
    def simplifyComplement(self, i):
        if not i:
            return self
        ei, ci = self.args[i]
        x, domain = ci.args
        
        union = self.union_domain(i) 

        A, B = domain.args
        if B in union:
            domain = A
            args = [*self.args]
            args[i] = (ei, ci.func(x, domain))
            return self.func(*args).simplify()
            
        return self
        
    def union_domain(self, i):
        _, ci = self.args[i]
        x, _ = ci.args
        
        union = x.emptySet
        for j in range(i):
            _, condition = self.args[j]
            union |= x.domain_conditioned(condition)
        return union
        
    def simplifyIntersection(self, i):
        if not i:
            return self
        ei, ci = self.args[i]
        x, domain = ci.args
        
        universe = x.domain
        union = self.union_domain(i)
        
        for j, s in enumerate(domain.args):
            hit = False
            if universe in s | union:
                args = [*domain.args]
                del args[j]                
                hit = True
            elif s.is_Complement:
                A, B = s.args
                if B in union:
                    args = [*domain.args]
                    args[j] = A
                    hit = True
                
            if hit:
                domain = domain.func(*args)
                args = [*self.args]
                args[i] = (ei, ci.func(x, domain))
                return self.func(*args).simplify()
            
        return self
        
    def simplify(self, deep=False, wrt=None):
        from sympy.functions.special.tensor_functions import KroneckerDelta
        if deep or wrt is not None:
            scope_variables = self.scope_variables
            if wrt is None:
                if len(scope_variables) == 1:
                    wrt, *_ = scope_variables
            else: 
                if wrt not in scope_variables:
                    if len(scope_variables) == 1:
                        wrt, *_ = scope_variables
                    else:
                        wrt = None
                            
            if wrt is not None: 
                univeralSet = wrt.domain
                args = []
                union = wrt.emptySet
#                 union_second_last = None
                hit = False
                need_swap = False
                for f, cond in self.args:
                    domain = (univeralSet - union) & wrt.domain_conditioned(cond)
                    if not cond:
#                         union_second_last = union
                        union |= domain
                    if domain.is_EmptySet:
                        if cond:
                            args[-1] = (args[-1][0], True)
                        else:
                            args.append((f, False))
                        hit = True
                        continue
                    
                    if f._has(wrt):
                        if domain.is_FiniteSet:
                            if len(domain) == 1:
                                if cond:
                                    need_swap = True
                                    hit = True
                                _x, *_ = domain.args
                            else:
                                _x = domain.args
                        else:
                            _x = wrt.copy(domain=domain)
                            
                        if isinstance(_x, tuple):
                            arglist = []
                            for x in _x:
                                eq = Equal(wrt, x)
                                if eq.is_BooleanFalse:
                                    continue
                                arglist.append([f._subs(wrt, x), eq])
                                
                            arglist[-1][-1] = True
                            if len(arglist) == 1:
                                _f = arglist[0][0].simplify(deep=deep)
                            else:
                                _f = Piecewise(*arglist).simplify(deep=deep)
                        else:
                            _f = f._subs(wrt, _x).simplify(deep=deep)._subs(_x, wrt)
                                                        
                        if _f != f:
                            hit = True
                            f = _f
                    args.append((f, cond))
                            
                if need_swap:
                    e_last, _ = args[-1]
                    e_second_last, _ = args[-2]
                    args[-2] = (e_last, Equal(wrt, _x))
                    args[-1] = (e_second_last, True)
                    
                if hit: 
                    return self.func(*args).simplify(deep=deep)
                        
            args = []
            hit = False
            for i, (e, c) in enumerate(self.args):
                _e = e.simplify(deep=deep)
                if _e != e:
                    e = _e
                    hit = True
                _c = c.simplify(deep=deep)
                if _c != c:
                    c = _c
                    hit = True
                args.append((e, c))
                
            if hit:
                return self.func(*args).simplify()
            
        expr, _ = self.args[-1]
        e, c = self.args[-2]
    
        if e == expr or c.is_Equal and (e == expr._subs(*c.args) or e._subs(*c.args) == expr):
            args = [*self.args]
            del args[-2]
            if len(args) == 1:
                return expr
            return self.func(*args).simplify()            
            
        if len(self.args) == 2:
            e0, c0 = self.args[0]
            e1, c1 = self.args[1]
            if deep:
                e0 = e0.simplify(deep=deep)
                e1 = e1.simplify(deep=deep)
            if c0.is_Equal:
                res = Piecewise.simplify_Equality(e0, e1, *c0.args)
                if res is not None:
                    return res
                                         
            if c0.is_Unequal:
                res = Piecewise.simplify_Equality(e1, e0, *c0.args)
                if res is not None:
                    return res
                
            from sympy.sets.contains import NotElement, Element
            if c0.is_Element:
                x, A = c0.args
                if A.is_FiniteSet:
                    args = []
                    for y in A.args:
                        delta = KroneckerDelta(x, y)
                        if delta != S.Zero:
                            args.append((e0._subs(x, y).simplify(), Equal(x, y)))
                            e1 = e1._subs(delta, S.Zero)
                    return self.func(*args, (e1, True)).simplify()
                
                if x.is_symbol:
                    domain = self.args[0].domain_defined(x)
                    if A.is_Complement:
                        U, C = A.args
                        if domain in U: 
                            return self.func((e0, NotElement(x, C)), (e1, True)).simplify(deep=deep)
                        complement = domain - A
                        if complement.is_FiniteSet:
                            return self.func((e1, Element(x, complement)), (e0, True)).simplify(deep=deep)
                    if domain in A:
                        if e1._has(x):
                            universe = self.domain_defined(x)
                            if universe != domain:
                                diff = universe - A
                                if diff.is_FiniteSet:
                                    return self.func((e1, Element(x, diff)), (e0, True)).simplify()
                                return self
                if e1.is_EmptySet:
                    if e0 == x.set:
                        return A & e0
            elif c0.is_NotElement: 
                return self.func((e1, c0.invert()), (e0, True)).simplify(deep=deep)
                
        if expr.is_Piecewise:
            if self.scope_variables & expr.scope_variables:
                args = [*self.args]
                args.pop()
                return self.func(*args, *expr.args).simplify(deep=deep)
        
        if len(self.scope_variables) == 1:
            for i, (e, c) in enumerate(self.args):
                if c.is_Element:
                    x, domain = c.args
                    if x in self.scope_variables:
                        if domain.is_Intersection:
                            return self.simplifyIntersection(i)
                        elif domain.is_Complement:
                            return self.simplifyComplement(i)
                        
        return self

    def __contains__(self, other):
        for e, _ in self.args:
            if other not in e:
                return False
        return True

    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices):
        return self.func(*((e[indices], c) for e, c in self.args))
        
    def sift(self, cond):
        cond = cond.invert()
        U = S.true
        for e, c in self.args:
            _c = c & U | cond
            if _c:
                return e
            U &= c.invert()
        return self
    
    def select_cond(self, expr):
        u = S.true
        for e, c in self.args: 
            eq = Equal(expr, e)                   
            if eq.is_BooleanFalse:
                ...
            elif eq:
                return u & c
            else:
                return
            u &= c.invert()
            
    def union_sets(self, b):
        tuples = []
        if b.is_Piecewise:
            if len(b.args) != len(self.args):
                return
            for (e, c), (_e, _c) in zip(self.args, b.args):
                if c != _c:
                    return
                e |= _e
                if e.is_Piecewise:
                    e = e.sift(c) 
                tuples.append((e, c))  
        else:
            for e, c in self.args:
                tuples.append((e | b, c))    
        return self.func(*tuples).simplify()

    def intersection_sets(self, b):
        if b.is_Piecewise:
            return
        tuples = []
        for e, c in self.args:
            tuples.append((e & b, c))    
        return self.func(*tuples)

    def _complement(self, universe):
        if universe.is_Piecewise: 
            return
        
        tuples = []
        for e, c in self.args:
            tuples.append((universe - e, c))    
        return self.func(*tuples)

    def mul(self, other, simplify=True):
        piece = []
        u = S.true
        for e, c in self.args:
            args = []
            _u = S.true
            c_ = c & u
            for _e, _c in other.args:
                _c_ = _c & _u
                _c_ = c_ & _c_
                
                if _c_.is_BooleanFalse:
                    continue
                args.append([(e * _e).simplify(), _c])
                _u &= _c.invert()
            if len(args) == 1:
                piece.append((args[-1][0], c))
            else:
                args[-1][-1] = True
                piece.append((self.func(*args).simplify(), c))
            u &= c.invert()

        self = self.func(*piece)
        if simplify:
            self = self.simplify()
        return self
        
    def add(self, other):
        piece = []
        u = S.true
        for e, c in self.args:
            args = []
            _u = S.true
            c_ = c & u
            for _e, _c in other.args:
                _c_ = _c & _u
                _c_ = c_ & _c_
                if _c_.is_BooleanFalse:
                    continue
                args.append([(e + _e).simplify(), _c])
                _u &= _c.invert()
            if len(args) == 1:
                piece.append((args[-1][0], c))
            else:
                args[-1][-1] = True
                piece.append((self.func(*args).simplify(), c))
            u &= c.invert()
        return self.func(*piece)
    
    def default_condition(self):
        u = S.true
        for _, c in self.args[:-1]: 
            u &= c.invert()    
        return u
        
    def try_add(self, other): 
        if self.default_condition() | other.default_condition():
            _ = self.args[-1][0]
            return self.func(*self.args[:-1], *((e + _, c) for e, c in other.args))

    def __bool__(self):
        if self.is_bool:
            return False
        return True
            
    def handle_finite_sets(self, unk):
        return self.func(*((e & unk, c) for e, c in self.args)).simplify()

    def _eval_is_finite(self):
        if all(e.is_finite for e, _ in self.args):
            return True
        
        if all(e.is_infinite for e, _ in self.args):
            return False

    def _pretty(pexpr, self):
        from sympy.printing.pretty.stringpict import prettyForm
        P = {}
        for n, ec in enumerate(pexpr.args):
            P[n, 0] = self._print(ec.expr)
            if ec.cond == True:
                P[n, 1] = prettyForm('else')
            else:
                P[n, 1] = prettyForm(
                    *prettyForm('if ').right(self._print(ec.cond)))
        hsep = 2
        vsep = 1
        len_args = len(pexpr.args)

        # max widths
        maxw = [max([P[i, j].width() for i in range(len_args)])
                for j in range(2)]

        # FIXME: Refactor this code and matrix into some tabular environment.
        # drawing result
        D = None

        for i in range(len_args):
            D_row = None
            for j in range(2):
                p = P[i, j]
                assert p.width() <= maxw[j]

                wdelta = maxw[j] - p.width()
                wleft = wdelta // 2
                wright = wdelta - wleft

                p = prettyForm(*p.right(' ' * wright))
                p = prettyForm(*p.left(' ' * wleft))

                if D_row is None:
                    D_row = p
                    continue

                D_row = prettyForm(*D_row.right(' ' * hsep))  # h-spacer
                D_row = prettyForm(*D_row.right(p))
            if D is None:
                D = D_row  # first row in a picture
                continue

            # v-spacer
            for _ in range(vsep):
                D = prettyForm(*D.below(' '))

            D = prettyForm(*D.below(D_row))

        D = prettyForm(*D.parens('{', ''))
        D.baseline = D.height() // 2
        D.binding = prettyForm.OPEN
        return D

    def _latex(self, p): 
        
        ecpairs = [r"{%s} & {\color{blue} {\text{if}}}\ \: {%s}" % (p._print(e), p._print(c)) for e, c in self.args[:-1]]
        if self.args[-1].cond == S.true:
            ecpairs.append(r"{%s} & {\color{blue} {\text{else}}}" % p._print(self.args[-1].expr))
        else:
            ecpairs.append(r"{%s} & {\color{blue} {\text{if}}}\ \: {%s}" % (p._print(self.args[-1].expr), p._print(self.args[-1].cond)))
        tex = r"\begin{cases} %s \end{cases}"
        return tex % r" \\".join(ecpairs)

    def _lean(self, p): 
        args = self.args
        (thenBranch, ifBranch), *args = args
        elseBranch = args[0][0] if len(args) == 1 else Piecewise(*args)
        return "if %s then %s else %s" % (p._print(ifBranch), p._print(thenBranch), p._print(elseBranch))

    def as_multiple_terms(self, x, domain, cls):
        universalSet = x.universalSet
        args = []
        union = x.emptySet
        assert x in self.scope_variables
        for f, condition in self.args:
            _domain = (universalSet - union) & x.domain_conditioned(condition) & domain
            if not condition:
                union |= _domain
    
            if _domain.is_FiniteSet:
                if _domain:
                    args.append(cls[x:_domain](f).simplify())
            elif _domain:
                if _domain.is_Range and _domain.step.is_One:
                    if x.is_integer:
                        a = _domain.start
                        b = _domain.stop
                        args.append(cls(f, (x, a, b)).simplify())
                    else:
                        args.append(cls(f, (x, _domain)).simplify())
                elif _domain.is_Interval: 
                    if x.is_integer:
                        _domain = _domain.copy(integer=True)   
                        a = _domain.start
                        b = _domain.stop
                        args.append(cls(f, (x, a, b)).simplify())    
                    else:
                        args.append(cls(f, (x, _domain)).simplify())
                else:
                    args.append(cls(f, (x, _domain)).simplify())
        return cls.operator(*args)

    def monotonicity(self, x):
        monotonicity = 0
        args = [[*args] for args in self.args]
        for i, (expr, _) in enumerate(args):
            if not expr._has(x):
                continue
            
            args[i][0], _monotonicity = expr.monotonicity(x) 
            if not _monotonicity:
                return None, 0
            
            if not monotonicity:
                monotonicity = _monotonicity
            elif monotonicity != _monotonicity:
                return None, 0
            
        return self.func(*args, evaluate=False), monotonicity

    def check_sanctity(self):        
        assert self.args[-1][1]
        
        for e, c in self.args:            
            for expr in e.preorder_traversal():
                if expr.is_Piecewise:
                    expr.check_sanctity()
         
    
    @staticmethod
    def simplify_Lamda(self, squeeze=False):
        limits_dict = self.limits_dict
        if len(limits_dict) > 1:
            expr = self.func(self.expr, self.limits[0]).simplify(squeeze=squeeze)
            if not expr.is_Stack:
                return self.func(expr, *self.limits[1:]).simplify(squeeze=squeeze)
            if not expr.expr.is_Piecewise:
                return self.func(expr.expr, *expr.limits, *self.limits[1:])
                
        else:
            if len(self.expr.args) == 2:
                e0, c0 = self.expr.args[0]
                if c0.is_Element:
                    e, s = c0.args
                    if e in limits_dict.keys():
                        if s.is_Complement:
                            U, A = s.args
                            domain, *_ = limits_dict.values()
                            if domain in U:
                                e1, _ = self.expr.args[1]
                                from sympy.sets.contains import Element
                                expr = self.expr.func((e1, Element(e, A)), (e0, True)).simplify()
                                return self.func(expr, *self.limits).simplify(squeeze=squeeze)
                        elif s.is_Range:
                            if limits_dict[e] in s:
                                return self.func(e0, *self.limits).simplify(squeeze=squeeze)
            if self.expr.is_set:
                return self
            
            args = []
            for e, c in self.expr.args:
                if not e._has(self.variable):
                    return self
                
                if c._has(self.variable):
                    return self
                
                this_old = self.func(e, *self.limits)
                this = this_old.simplify()
                if this == this_old:
                    return self
                
                args.append((this, c))
                
            return self.expr.func(*args)
        
        return self
                
    @cacheit
    def sort_key(self, order=None):
        args = self.args
        args = tuple(arg.sort_key(order=order) for arg in args)
        args = len(args), tuple(arg.class_key() for arg in self.args), args
        
        return self.class_key(), args, S.One.sort_key(order=order), S.One

    @classmethod
    def class_key(cls):
        return 5, 100, cls.__name__

    @property
    def T(self):
        return self.func(*((e.T, c) for e, c in self.args))


def piecewise_fold(expr):
    """
    Takes an expression containing a piecewise function and returns the
    expression in piecewise form. In addition, any ITE conditions are
    rewritten in negation normal form and simplified.

    Examples
    ========

    >>> from sympy import Piecewise, piecewise_fold, sympify as S
    >>> from sympy.abc import x
    >>> p = Piecewise((x, x < 1), (1, S(1) <= x))
    >>> piecewise_fold(x*p)
    Piecewise((x**2, x < 1), (x, True))

    See Also
    ========

    Piecewise
    """
    if not isinstance(expr, Basic) or not expr.has(Piecewise) or expr.is_ExprWithLimits:
        return expr

    new_args = []
    if isinstance(expr, (ExprCondPair, Piecewise)):
        for e, c in expr.args:
            if not isinstance(e, Piecewise):
                e = piecewise_fold(e)
            # we don't keep Piecewise in condition because
            # it has to be checked to see that it's complete
            # and we convert it to ITE at that time
            assert not c.has(Piecewise)  # pragma: no cover
            if isinstance(c, ITE):
                c = c.to_nnf()
                c = simplify_logic(c, form='cnf')
            new_args.append((e, c))
#             if isinstance(e, Piecewise):
#                 new_args.extend([(piecewise_fold(ei), And(ci, c)) for ei, ci in e.args])
#             else:
#                 new_args.append((e, c))
    else:
        from sympy.utilities.iterables import cartes, sift, common_prefix
        # Given
        #     P1 = Piecewise((e11, c1), (e12, c2), A)
        #     P2 = Piecewise((e21, c1), (e22, c2), B)
        #     ...
        # the folding of f(P1, P2) is trivially
        # Piecewise(
        #   (f(e11, e21), c1),
        #   (f(e12, e22), c2),
        #   (f(Piecewise(A), Piecewise(B)), True))
        # Certain objects end up rewriting themselves as thus, so
        # we do that grouping before the more generic folding.
        # The following applies this idea when f = Add or f = Mul
        # (and the expression is commutative).
#         if expr.is_Add or expr.is_Mul and expr.is_commutative:
        if expr.is_Add or expr.is_Mul:
            p, args = sift(expr.args, lambda x: x.is_Piecewise, binary=True)
            if len(p) > 1:
                return expr
            pc = sift(p, lambda x: tuple([c for e, c in x.args]))
            for c in list(ordered(pc)):
                if len(pc[c]) > 1:
                    pargs = [list(i.args) for i in pc[c]]
                    # the first one is the same; there may be more
                    com = common_prefix(*[
                        [i.cond for i in j] for j in pargs])
                    n = len(com)
                    collected = []
                    for i in range(n):
                        collected.append((
                            expr.func(*[ai[i].expr for ai in pargs]),
                            com[i]))
                    remains = []
                    for a in pargs:
                        if n == len(a):  # no more args
                            continue
                        if a[n].cond == True:  # no longer Piecewise
                            remains.append(a[n].expr)
                        else:  # restore the remaining Piecewise
                            remains.append(
                                Piecewise(*a[n:], evaluate=False))
                    if remains:
                        collected.append((expr.func(*remains), True))
                    args.append(Piecewise(*collected, evaluate=False))
                    continue
                args.extend(pc[c])
        else:
            args = expr.args
        # fold
        folded = list(map(piecewise_fold, args))
        for ec in cartes(*[(i.args if isinstance(i, Piecewise) else [(i, S.true)]) for i in folded]):
            e, c = zip(*ec)
            new_args.append((expr.func(*e), And(*c)))

    return Piecewise(*new_args)


def _clip(A, B, k):
    """Return interval B as intervals that are covered by A (keyed
    to k) and all other intervals of B not covered by A keyed to -1.

    The reference point of each interval is the rhs; if the lhs is
    greater than the rhs then an interval of zero width interval will
    result, e.g. (4, 1) is treated like (1, 1).

    Examples
    ========

    >>> from sympy.functions.elementary.piecewise import _clip
    >>> from sympy import Tuple
    >>> A = Tuple(1, 3)
    >>> B = Tuple(2, 4)
    >>> _clip(A, B, 0)
    [(2, 3, 0), (3, 4, -1)]

    Interpretation: interval portion (2, 3) of interval (2, 4) is
    covered by interval (1, 3) and is keyed to 0 as requested;
    interval (3, 4) was not covered by (1, 3) and is keyed to -1.
    """
    a, b = B
    c, d = A
    c, d = Min(Max(c, a), b), Min(Max(d, a), b)
    a, b = Min(a, b), b
    p = []
    if a != c:
        p.append((a, c, -1))
    else:
        pass
    if c != d:
        p.append((c, d, k))
    else:
        pass
    if b != d:
        if d == c and p and p[-1][-1] == -1:
            p[-1] = p[-1][0], b, -1
        else:
            p.append((d, b, -1))
    else:
        pass

    return p
