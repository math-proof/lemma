import Mathlib.Analysis.Calculus.Gradient.Basic

/-- Strip outer term parentheses so `∇[θ] (F θ)` and `∇[θ] F θ` share one match. -/
private partial def GradSugar.stripParen : Lean.TSyntax `term → Lean.MacroM (Lean.TSyntax `term)
  | `(($e)) => stripParen e
  | e => pure e

/--
[sympy.Gradient](https://github.com/sympy/sympy/blob/master/sympy/vector/operators.py)

`∇` is an unscoped alias for Mathlib's `gradient` (same as scoped `Gradient.«term∇»`).

`∇[θ] body` is the gradient of `body` with respect to `θ`, evaluated at the `θ` in scope.
Eta rule: if `body` is (after stripping parentheses) an application `F θ` whose argument is the
bracket binder, or a bare name `F`, it elaborates to `gradient F θ` with **no** fresh binder, so
outer instances (e.g. `PSpace (M θ) …`) stay in scope. Otherwise it elaborates to
`gradient (fun θ ↦ body) θ` (open-term form). Multi-arg apps such as `M.policy.prob θ x u` do not
match the eta rule (outermost argument is not `θ`) and keep the lambda path.

The point form `∇[θ = θ₀] body` is the same with evaluation point `θ₀` (elaborated outside any
binder, as in `Subst`): eta `F θ` / bare `F` → `gradient F θ₀`; else `gradient (fun θ ↦ body) θ₀`.
So `Subst (∇[θ] body | θ = θ₀) = ∇[θ = θ₀] body` by `rfl` on the open-term path.

The body of `∇[…]` is parsed at `term:67`, like the body of Mathlib's `∑ x, f x`: it extends over
application, `*`, `/`, `•`, `^`, but stops before `+`, `-`, `=`, `∧`, `|`, … So `∇[θ] f θ • v` is
`∇[θ] (f θ • v)`, while `∇[θ] f θ + c` is `(∇[θ] f θ) + c`. The token `∇[` does not clash with
binder-free `∇` (or Mathlib's scoped `∇ f`), which needs a space or a non-`[` argument after `∇`.
-/
notation:max "∇" => gradient

syntax:max (name := gradSugar) "∇[" ident "] " term:67 : term

/-- `∇[θ = θ₀] expr`: the gradient of `expr` with respect to `θ`, evaluated at `θ₀`. -/
syntax:max (name := gradAtSugar) "∇[" ident " = " term "] " term:67 : term

macro_rules
  | `(∇[$x:ident] $body) => do
    let b ← GradSugar.stripParen body
    match b with
    | `($f $y:ident) =>
      if y.getId == x.getId then
        `(gradient $f $x)
      else
        `(gradient (fun $x:ident ↦ $body) $x)
    | `($j:ident) =>
      `(gradient $j $x)
    | _ =>
      `(gradient (fun $x:ident ↦ $body) $x)
  | `(∇[$x:ident = $p] $body) => do
    let b ← GradSugar.stripParen body
    match b with
    | `($f $y:ident) =>
      if y.getId == x.getId then
        `(gradient $f $p)
      else
        `(gradient (fun $x:ident ↦ $body) $p)
    | `($j:ident) =>
      `(gradient $j $p)
    | _ =>
      `(gradient (fun $x:ident ↦ $body) $p)

/-- Infoview: `gradient (fun θ ↦ e) θ` ↦ `∇[θ] e`; `gradient (fun θ ↦ e) p` ↦ `∇[θ = p] e`;
non-lambda `gradient F p` with `p` an ident ↦ `∇[p] (F p)`. -/
@[app_unexpander gradient]
def gradient.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $p) =>
    match f with
    | `(fun $x:ident ↦ $body) => do
      if let `($y:ident) := p then
        if x.getId == y.getId then return ← `(∇[$x] $body)
      `(∇[$x = $p] $body)
    | _ => do
      if let `($y:ident) := p then
        return ← `(∇[$y] ($f $y))
      `(∇ $f $p)
  | _ => throw ()
