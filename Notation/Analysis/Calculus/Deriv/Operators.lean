import Mathlib.Analysis.Calculus.Deriv.Basic


/-!
Partial / ordinary derivative sugar mirroring `∇[θ]` (see
`Notation.Analysis.Calculus.Gradient.Operators`).

`∂[t] body` is the derivative of `body` with respect to `t`, evaluated at the `t` in scope.
Eta rule: if `body` is (after stripping parentheses) an application `F t` whose argument is the
bracket binder, or a bare name `F`, it elaborates to `deriv F t` with **no** fresh binder, so
outer instances stay in scope. Otherwise it elaborates to `deriv (fun t ↦ body) t` (open-term
form). Multi-arg apps such as `u t x` do not match the eta rule (outermost argument is not `t`)
and keep the lambda path. Example: `∂[t] f t = deriv f t` and
`∂[t] (A * cos (ω * t) + B * sin (ω * t)) = deriv (fun t ↦ A * cos (ω * t) + B * sin (ω * t)) t`.

The point form `∂[t = t₀] body` is the same with evaluation point `t₀` (elaborated outside any
binder, as in `Subst`): eta `F t` / bare `F` → `deriv F t₀`; else `deriv (fun t ↦ body) t₀`.

The body of `∂[…]` is parsed at `term:67`, like `∇[…]` and Mathlib's `∑ x, f x`: it extends over
application, `*`, `/`, `•`, `^`, but stops before `+`, `-`, `=`, `∧`, `|`, … So
`∂[t] f t * c` is `∂[t] (f t * c)`, while `∂[t] f t + c` is `(∂[t] f t) + c`.

There is **no** binder-free unscoped `∂` alias for `deriv`: Mathlib already uses `∂` in measure
binders (`∫ x, f x ∂μ`, with a space before `∂`) and in `∂P/∂Q` (Radon–Nikodym). The token `∂[`
does not clash with those (integral / RN forms are not followed by `[`).
-/
