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

theorem ReducedArgMax.append_eq_ite {m n : ℕ} [NeZero m] [NeZero n]
    {x : Fin m → ℝ}
    {y : Fin n → ℝ} :
    ReducedArgMax (Fin.append x y) =
      if Function.max y > Function.max x then Fin.natAdd m (ReducedArgMax y)
      else Fin.castAdd n (ReducedArgMax x) := by
  have hx_le : ∀ i, x i ≤ Function.max x :=
    fun i => Finset.le_sup' x (Finset.mem_univ i)
  have hy_le : ∀ j, y j ≤ Function.max y :=
    fun j => Finset.le_sup' y (Finset.mem_univ j)
  have hrx_eq : x (ReducedArgMax x) = Function.max x := ReducedArgMax.eq_max x
  have hry_eq : y (ReducedArgMax y) = Function.max y := ReducedArgMax.eq_max y
  if hgt : Function.max y > Function.max x then
    have hry_le : ∀ j, y j ≤ y (ReducedArgMax y) := fun j => by rw [hry_eq]; exact hy_le j
    have hc_val : (Fin.append x y) (Fin.natAdd m (ReducedArgMax y)) = y (ReducedArgMax y) := by
      simp only [Fin.append_right]
    have hc_max : ∀ j, (Fin.append x y) j ≤ y (ReducedArgMax y) := by
      intro j
      induction j using Fin.addCases with
      | left i =>
        simp only [Fin.append_left]
        rw [hry_eq]
        exact ((hx_le i).trans_lt hgt).le
      | right j =>
        simp only [Fin.append_right]
        exact hry_le j
    have hc_max' : ∀ j,
        (Fin.append x y) j ≤ (Fin.append x y) (Fin.natAdd m (ReducedArgMax y)) := by
      intro j
      rw [hc_val]
      exact hc_max j
    have hc_first : ∀ i,
        (∀ k, (Fin.append x y) k ≤ (Fin.append x y) i) →
        (Fin.natAdd m (ReducedArgMax y) : Fin (m + n)) ≤ i := by
      intro i hi
      induction i using Fin.addCases with
      | left i' =>
        simp only [Fin.append_left] at hi
        exact (by linarith [hry_eq, hx_le i', hgt, hc_val ▸ hi (Fin.natAdd m (ReducedArgMax y))] : False).elim
      | right j' =>
        simp only [Fin.append_right] at hi
        have hj'_le : y j' ≤ y (ReducedArgMax y) := hry_le j'
        have hi_j' : y (ReducedArgMax y) ≤ y j' := by
          rw [← hc_val]
          exact hi (Fin.natAdd m (ReducedArgMax y))
        have hj'_eq : y j' = y (ReducedArgMax y) := le_antisymm hj'_le hi_j'
        have hj'_max : ∀ k, y k ≤ y j' := by
          intro k
          rw [hj'_eq]
          exact hry_le k
        apply (Fin.strictMono_natAdd m).le_iff_le.mpr
        exact ReducedArgMax.le_of_forall_le y hj'_max
    rw [ite_eq_left hgt]
    refine le_antisymm ?_ ?_
    · exact ReducedArgMax.le_of_forall_le _ hc_max'
    · exact hc_first _ (ReducedArgMax.le _)
  else
    have hle : Function.max y ≤ Function.max x := not_lt.mp hgt
    have hrx_le : ∀ i, x i ≤ x (ReducedArgMax x) := fun i => by rw [hrx_eq]; exact hx_le i
    have hry_le : ∀ j, y j ≤ y (ReducedArgMax y) := fun j => by rw [hry_eq]; exact hy_le j
    have hc_val : (Fin.append x y) (Fin.castAdd n (ReducedArgMax x)) = x (ReducedArgMax x) := by
      simp only [Fin.append_left]
    have hc_max : ∀ j, (Fin.append x y) j ≤ x (ReducedArgMax x) := by
      intro j
      induction j using Fin.addCases with
      | left i =>
        simp only [Fin.append_left]
        exact hrx_le i
      | right j =>
        simp only [Fin.append_right]
        exact (hy_le j).trans (hle.trans hrx_eq.symm.le)
    have hc_max' : ∀ j,
        (Fin.append x y) j ≤ (Fin.append x y) (Fin.castAdd n (ReducedArgMax x)) := by
      intro j
      rw [hc_val]
      exact hc_max j
    have hc_first : ∀ i,
        (∀ k, (Fin.append x y) k ≤ (Fin.append x y) i) →
        (Fin.castAdd n (ReducedArgMax x) : Fin (m + n)) ≤ i := by
      intro i hi
      induction i using Fin.addCases with
      | left i' =>
        simp only [Fin.append_left] at hi
        have hxi'_max : ∀ k, x k ≤ x i' := by
          intro k
          have := hi (Fin.castAdd n k)
          rwa [Fin.append_left] at this
        apply (Fin.strictMono_castAdd n).le_iff_le.mpr
        exact ReducedArgMax.le_of_forall_le x hxi'_max
      | right j' =>
        simp only [Fin.append_right] at hi
        show (ReducedArgMax x).val ≤ m + j'.val
        exact (ReducedArgMax x).isLt.le.trans (Nat.le_add_right _ _)
    rw [ite_eq_right hgt]
    refine le_antisymm ?_ ?_
    · exact ReducedArgMax.le_of_forall_le _ hc_max'
    · exact hc_first _ (ReducedArgMax.le _)


-- created on 2026-10-02