import Mathlib.Analysis.Calculus.Gradient.Basic
import Def.Analysis.Calculus.Gradient.Operators


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

