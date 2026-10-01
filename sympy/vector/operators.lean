import Mathlib.Analysis.Calculus.Gradient.Basic

/--
[sympy.Gradient](https://github.com/sympy/sympy/blob/master/sympy/vector/operators.py)

`∇[θ] expr` is the gradient of `expr` with respect to `θ`, evaluated at the `θ` in scope:
it elaborates to Mathlib's `gradient (fun θ ↦ expr) θ` (sympy `gradient(expr)` / `Del()(expr)`).
The point form `∇[θ = θ₀] expr` evaluates at `θ₀` instead: it is `gradient (fun θ ↦ expr) θ₀`, with `θ₀`
elaborated outside the binder (as in `Subst`); so `Subst (∇[θ] expr | θ = θ₀) = ∇[θ = θ₀] expr` by `rfl`.
Inside the brackets the point is a full term up to `]`.

The body is parsed at `term:67`, like the body of Mathlib's `∑ x, f x`: it extends over application,
`*`, `/`, `•`, `^`, but stops before `+`, `-`, `=`, `∧`, `|`, … So `∇[θ] f θ • v` is `∇[θ] (f θ • v)`,
while `∇[θ] f θ + c` is `(∇[θ] f θ) + c`. The token `∇[` does not clash with Mathlib's scoped
`Gradient.«term∇»` (`∇ f`), which needs a space or a non-`[` argument after `∇`.
-/
syntax:max (name := gradSugar) "∇[" ident "] " term:67 : term

/-- `∇[θ = θ₀] expr`: the gradient of `expr` with respect to `θ`, evaluated at `θ₀`. -/
syntax:max (name := gradAtSugar) "∇[" ident " = " term "] " term:67 : term

macro_rules
  | `(∇[$x:ident] $body) => `(gradient (fun $x:ident ↦ $body) $x)
  | `(∇[$x:ident = $p] $body) => `(gradient (fun $x:ident ↦ $body) $p)

/-- Infoview: `gradient (fun θ ↦ e) θ` ↦ `∇[θ] e` when the point is the bound name itself, and
`gradient (fun θ ↦ e) p` ↦ `∇[θ = p] e` otherwise; `gradient f p` (no lambda) is left as is. -/
@[app_unexpander gradient]
def gradient.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $p) => do
    -- the delaborated lambda is not yet parenthesized here
    let `(fun $x:ident ↦ $body) := f | throw ()
    if let `($y:ident) := p then
      if x.getId == y.getId then return ← `(∇[$x] $body)
    `(∇[$x = $p] $body)
  | _ => throw ()
