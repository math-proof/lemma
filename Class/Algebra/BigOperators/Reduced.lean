import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finset.Max


/-!
Vector-style reductions on functions `α → β` over a finite index type, so that a vector
`v : α → ℝ` (e.g. `x' t + G a`, with `+` the pointwise `Pi.add`) or a matrix with a broadcast
vector (`G + x' t`) can be written the way py writes it, via dot notation (`Function` is the namespace for function-typed heads):

* `v.exp`  : `fun b => Real.exp (v b)`        (py `Exp(v)`)
* `v.log`  : `fun b => Real.log (v b)`        (py `Log(v)`)
* `v.sum`  : `∑ b, v b`                        (py `ReducedSum(v)`)
* `v.max`  : `Finset.univ.sup' _ v`, per row for a matrix (py `ReducedMax(v)`, needs `[Nonempty α]`)
* `ReducedArgMax v` : the FIRST index attaining the maximum of `v` (py `ReducedArgMax(v)`, needs `[LinearOrder α]`, `[Fintype α]`, `[Nonempty α]`; not dot-notation `v.argmax`, which is Mathlib's well-founded variant)

`exp`, `log`, `sum`, `max` unfold by `rfl` (and are `@[simp]`-unfoldable through the `*_apply` / `sum_eq` lemmas).
-/

/-- Types on which a real function can be applied entrywise: `ℝ` itself, and functions into such a type. -/
class Function.Elementwise (β : Type*) where
  map : (ℝ → ℝ) → β → β

