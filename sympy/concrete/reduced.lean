import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max

/-!
Vector-style reductions on functions `α → β` over a finite index type, so that a vector
`v : α → ℝ` (e.g. `x' t + G a`, with `+` the pointwise `Pi.add`) can be written the way py
writes it, via dot notation (`Function` is the namespace for function-typed heads):

* `v.exp`  : `fun b => Real.exp (v b)`        (py `Exp(v)`)
* `v.log`  : `fun b => Real.log (v b)`        (py `Log(v)`)
* `v.sum`  : `∑ b, v b`                        (py `ReducedSum(v)`)
* `v.max`  : `Finset.univ.sup' _ v`            (py `ReducedMax(v)`, needs `[Nonempty α]`)

All four unfold by `rfl` (and are `@[simp]`-unfoldable through the `*_apply` / `sum_eq` lemmas).
-/

/-- `v.exp = (fun b => (v b).exp)`. -/
noncomputable def Function.exp {α : Type*} (v : α → ℝ) : α → ℝ := fun b => Real.exp (v b)

/-- `v.log = (fun b => (v b).log)`. -/
noncomputable def Function.log {α : Type*} (v : α → ℝ) : α → ℝ := fun b => Real.log (v b)

/-- `v.sum = ∑ b, v b` (py `ReducedSum`). -/
def Function.sum {α β : Type*} [Fintype α] [AddCommMonoid β] (v : α → β) : β := ∑ b, v b

/-- `v.max = max_b v b` (py `ReducedMax`). -/
def Function.max {α β : Type*} [Fintype α] [Nonempty α] [SemilatticeSup β] (v : α → β) : β :=
  Finset.univ.sup' Finset.univ_nonempty v

@[simp] theorem Function.exp_apply {α : Type*} (v : α → ℝ) (b : α) : v.exp b = Real.exp (v b) := rfl

@[simp] theorem Function.log_apply {α : Type*} (v : α → ℝ) (b : α) : v.log b = Real.log (v b) := rfl

theorem Function.sum_eq {α β : Type*} [Fintype α] [AddCommMonoid β] (v : α → β) :
    v.sum = ∑ b, v b := rfl

theorem Function.max_eq {α β : Type*} [Fintype α] [Nonempty α] [SemilatticeSup β] (v : α → β) :
    v.max = Finset.univ.sup' Finset.univ_nonempty v := rfl


-- created on 2026-10-02