import Mathlib.Algebra.Group.ForwardDiff

/-- sympy `Difference(f(x), (x, n))`: the `n`-th forward difference with unit step, realized by Mathlib's `fwdDiff 1` iterated `n` times. -/
abbrev Difference {M G : Type*} [AddCommMonoid M] [One M] [AddCommGroup G] (f : M → G) (n : ℕ) : M → G :=
  (fwdDiff (1 : M))^[n] f

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

@[simp]
theorem Subst.eq_app {α : Sort*} {β : Sort*} (f : α → β) (a : α) : «Subst» f a = f a :=
  rfl

/-- One substitution `x = x₀` in the `Subst` sugar. -/
syntax substBinding := ident ppHardSpace "=" ppHardSpace term:36

/-- `Subst (expr | x = x₀ ∧ y = y₀)`: simultaneous substitution `x := x₀`, `y := y₀` in `expr`. -/
syntax:max (name := substSugar) "Subst" ppHardSpace "(" term ppHardSpace "|" ppSpace sepBy1(substBinding, " ∧ ") ")" : term

/-- `Subst f x₀ …`: plain application of the constant `«Subst»` (the name `Subst` is a keyword). -/
syntax:max (name := substApp) "Subst" (ppSpace colGt term:max)+ : term

macro_rules
  | `(Subst ($body | $bs∧*)) => do
    let bs := bs.getElems
    let xs ← bs.mapM fun
      | `(substBinding| $x:ident = $_) => pure x
      | _ => Lean.Macro.throwUnsupported
    let vs ← bs.mapM fun
      | `(substBinding| $_:ident = $v) => pure v
      | _ => Lean.Macro.throwUnsupported
    -- with `n` values, `Subst f x₀ : β` is applied to `n - 1` more: fix `β := _ → ⋯ → _` up front so the
    -- application elaborates before `f` does
    let mut β ← `(_)
    for _ in vs[1:] do
      β ← `(_ → $β)
    `(«Subst» (β := $β) (fun $xs* ↦ $body) $vs*)

macro_rules
  | `(Subst $args*) => `(«Subst» $args*)

/-- Infoview: `Subst (fun x y ↦ expr) x₀ y₀` ↦ `Subst (expr | x = x₀ ∧ y = y₀)`; any other
application is shown as `Subst f …`. -/
@[app_unexpander «Subst»]
def Subst.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $vs*) => do
    -- the delaborated lambda is not yet parenthesized here
    if let `(fun $xs:ident* ↦ $body) := f then
      if xs.size == vs.size then
        let bs ← (xs.zip vs).mapM fun (x, v) => `(substBinding| $x:ident = $v)
        return ← `(Subst ($body | $bs∧*))
    `(Subst $f $vs*)
  | _ => throw ()
