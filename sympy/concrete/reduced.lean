import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max

/-!
Vector-style reductions on functions `α → β` over a finite index type, so that a vector
`v : α → ℝ` (e.g. `x' t + G a`, with `+` the pointwise `Pi.add`) or a matrix with a broadcast
vector (`G + x' t`) can be written the way py writes it, via dot notation (`Function` is the namespace for function-typed heads):

* `v.exp`  : `fun b => Real.exp (v b)`        (py `Exp(v)`)
* `v.log`  : `fun b => Real.log (v b)`        (py `Log(v)`)
* `v.sum`  : `∑ b, v b`                        (py `ReducedSum(v)`)
* `v.max`  : `Finset.univ.sup' _ v`, per row for a matrix (py `ReducedMax(v)`, needs `[Nonempty α]`)

All four unfold by `rfl` (and are `@[simp]`-unfoldable through the `*_apply` / `sum_eq` lemmas).
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


-- created on 2026-10-02