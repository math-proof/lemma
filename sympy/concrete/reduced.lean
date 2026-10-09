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

instance : Function.Elementwise ℝ := ⟨fun f x => f x⟩

instance {α β : Type*} [Function.Elementwise β] : Function.Elementwise (α → β) :=
  ⟨fun f v a => Function.Elementwise.map f (v a)⟩

/-- Reduction along the last axis: a vector `α → ℝ` reduces to a scalar, a matrix `α → β → ℝ` to a vector. -/
class Function.Reduce (γ : Type*) (δ : outParam (Type*)) where
  reduce : γ → δ

instance {α : Type*} [Fintype α] : Function.Reduce (α → ℝ) ℝ := ⟨fun v => ∑ b, v b⟩

instance {α γ δ : Type*} [Function.Reduce γ δ] : Function.Reduce (α → γ) (α → δ) :=
  ⟨fun v a => Function.Reduce.reduce (v a)⟩

/-- Maximum along the last axis: a vector `α → ℝ` reduces to a scalar, a matrix `α → β → ℝ` to a vector. -/
class Function.ReduceMax (γ : Type*) (δ : outParam (Type*)) where
  reduce : γ → δ

instance {α : Type*} [Fintype α] [Nonempty α] : Function.ReduceMax (α → ℝ) ℝ :=
  ⟨fun v => Finset.univ.sup' Finset.univ_nonempty v⟩

instance {α γ δ : Type*} [Function.ReduceMax γ δ] : Function.ReduceMax (α → γ) (α → δ) :=
  ⟨fun v a => Function.ReduceMax.reduce (v a)⟩

/-- Broadcasting: `(f + c) a = f a + c`, e.g. a matrix `G : α → β → ℝ` plus a vector `v : β → ℝ`
is `fun a b => G a b + v b` (py `G + v`). -/
instance {α γ : Type*} [Add γ] : HAdd (α → γ) γ (α → γ) := ⟨fun f c a => f a + c⟩

/-- `v.exp = (fun b => (v b).exp)`, entrywise (py `Exp(v)`). -/
noncomputable def Function.exp {α β : Type*} [Function.Elementwise β] (v : α → β) : α → β :=
  fun b => Function.Elementwise.map Real.exp (v b)

/-- `v.log = (fun b => (v b).log)`, entrywise (py `Log(v)`). -/
noncomputable def Function.log {α β : Type*} [Function.Elementwise β] (v : α → β) : α → β :=
  fun b => Function.Elementwise.map Real.log (v b)

/-- `v.sum = ∑ b, v b` for a vector, and the row sums for a matrix (py `ReducedSum`). -/
def Function.sum {α β δ : Type*} [Function.Reduce (α → β) δ] (v : α → β) : δ :=
  Function.Reduce.reduce v

/-- `v.max = max_b v b` for a vector, and the row maxima (over the last axis) for a matrix (py `ReducedMax`). -/
def Function.max {α β δ : Type*} [Function.ReduceMax (α → β) δ] (v : α → β) : δ :=
  Function.ReduceMax.reduce v

@[simp] theorem Function.exp_apply {α : Type*} (v : α → ℝ) (b : α) : v.exp b = Real.exp (v b) := rfl

@[simp] theorem Function.log_apply {α : Type*} (v : α → ℝ) (b : α) : v.log b = Real.log (v b) := rfl


@[simp] theorem Function.max_apply {α β : Type*} [Fintype β] [Nonempty β] (v : α → β → ℝ) (a : α) :
    v.max a = (v a).max := rfl


/-- py `ReducedArgMax(v)`: the FIRST index attaining the maximum of `v`; py's `_eval_ReducedArgMax`
scans left-to-right keeping only strict improvements `val > M`, so on ties the earliest index wins.
(Named after py since Mathlib's `Function.argmax` is the well-founded variant.) -/
noncomputable def ReducedArgMax {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α] (v : α → ℝ) :
    α :=
  (Finset.univ.filter fun i => ∀ j, v j ≤ v i).min' (by
    obtain ⟨i, hi⟩ := Finite.exists_max v
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)

theorem ReducedArgMax.le {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α] (v : α → ℝ) (j : α) :
    v j ≤ v (ReducedArgMax v) := by
  have h : ReducedArgMax v ∈ Finset.univ.filter fun i => ∀ j, v j ≤ v i :=
    Finset.min'_mem _ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h j

theorem ReducedArgMax.le_of_forall_le {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (v : α → ℝ) {i : α} (hi : ∀ j, v j ≤ v i) : ReducedArgMax v ≤ i :=
  Finset.min'_le _ _ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)

theorem ReducedArgMax.eq_max {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (v : α → ℝ) : v (ReducedArgMax v) = Function.max v := by
  show v (ReducedArgMax v) = Finset.univ.sup' Finset.univ_nonempty v
  refine le_antisymm ?_ ?_
  · exact Finset.le_sup' v (Finset.mem_univ _)
  · apply Finset.sup'_le Finset.univ_nonempty v
    intro j _
    exact ReducedArgMax.le v j


-- created on 2026-10-02