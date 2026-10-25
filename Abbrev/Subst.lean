import Mathlib.Data.Nat.Basic

/--
[sympy.Subs](https://github.com/sympy/sympy/blob/master/sympy/core/function.py)

Unevaluated substitution: `Subst (fun x ↦ expr) x₀` is `expr` with `x := x₀`, written with the sugar
`Subst (expr | x = x₀)` (sympy `Subs(expr, x, x0)`).

Several variables are substituted *simultaneously* (sympy `Subs(expr, (x, y), (x0, y0))`):
`Subst (expr | x = x₀ ∧ y = y₀)` is `Subst (fun x y ↦ expr) x₀ y₀`, i.e. `(fun x y ↦ expr) x₀ y₀`, so the
values `x₀, y₀` are elaborated outside the binders (a free `x` in `y₀` is *not* replaced by `x₀`).
As in the `ℙ[π](… | x = u ∧ y = v)` sugar, `∧` joins the point equalities. Each value is parsed at
`term:36`, just above `∧` (`infixr:35`), so `Subst (f x y | x = n + 1 ∧ y = -2)` needs no parentheses,
while a value containing `∧`, `∨`, `→`, `↔` (or `fun`/`let` …) must be parenthesized. A relation inside a
value binds into the value: `Subst (p x | x = a = b)` substitutes the proposition `a = b` for `x`.

`Subst` is reducible, so `Subst f a = f a` holds by `rfl`; `simp` unfolds it via `Subst.eq_app`.

`Subst` is a keyword (so that `Subst (… | …)` parses): the constant itself is `«Subst»`, and both
`Subst (expr | x = x₀)` and the plain application `Subst f x₀` are accepted. Dotted names such as
`Subst.eq_app` are unaffected. In the sugar the body is a full term ending at the first top-level `|`,
so a body containing a bare `|` (e.g. a `match` alternative) must be parenthesized; `|x|` (abs),
`ℙ[π](… | …)` and `𝔼[…](… | …)` are self-delimited and need no parentheses.
-/
abbrev «Subst» {α : Sort*} {β : Sort*} (f : α → β) (a : α) : β :=
  f a
