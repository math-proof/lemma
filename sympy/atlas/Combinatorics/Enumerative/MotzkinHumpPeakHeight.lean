/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinHumpPeakHeight.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

namespace MetaMathlibExt

open scoped BigOperators

/-- Step height change: `0` is down, `1` is flat, `2` is up. -/
private def mhStep : Fin 3 → ℤ := fun s => (s.val : ℤ) - 1

/-- Copy of the Wanted `IsMotzkin` predicate with `mhStep`. -/
private def mhIsMotzkin (n : ℕ) (p : Fin n → Fin 3) : Prop :=
  (∀ m : ℕ, m ≤ n →
    0 ≤ ∑ i : Fin n, if i.val < m then mhStep (p i) else 0) ∧
  ∑ i : Fin n, mhStep (p i) = 0

/-- Copy of the Wanted `IsHump` predicate with `mhStep`. -/
private def mhIsHump (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  i.val < j.val ∧
  mhStep (p i) = 1 ∧
  mhStep (p j) = -1 ∧
  (∀ r : Fin n, i.val < r.val → r.val < j.val → mhStep (p r) = 0) ∧
  (∑ r : Fin n, if r.val ≤ i.val then mhStep (p r) else 0) = (k : ℤ)

/-- Copy of the Wanted `IsPeak` predicate with `mhStep`. -/
private def mhIsPeak (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  mhIsHump n k p i j ∧ j.val = i.val + 1

/-- Number of nonnegative Motzkin prefixes of length `L` ending at height `h`. -/
private def mhCount : ℕ → ℤ → ℕ
  | 0, h => if h = 0 then 1 else 0
  | L + 1, h => if h < 0 then 0 else mhCount L (h - 1) + mhCount L h + mhCount L (h + 1)

/-- Number of nonnegative flat-free (Dyck-like) prefixes of length `d` ending at `h`. -/
private def mhDyckCount : ℕ → ℤ → ℕ
  | 0, h => if h = 0 then 1 else 0
  | d + 1, h => if h < 0 then 0 else mhDyckCount d (h - 1) + mhDyckCount d (h + 1)

/-- Step of `p` at index `r`, or `0` past the end. -/
private def mhStepAt {L : ℕ} (p : Fin L → Fin 3) (r : ℕ) : ℤ :=
  if h : r < L then mhStep (p ⟨r, h⟩) else 0

/-- Height of `p` after `m` steps. -/
private def mhHeight {L : ℕ} (p : Fin L → Fin 3) (m : ℕ) : ℤ :=
  ∑ r ∈ Finset.range m, mhStepAt p r

/-- `p` stays nonnegative and ends at height `h`. -/
private def mhPrefixGood {L : ℕ} (p : Fin L → Fin 3) (h : ℤ) : Prop :=
  (∀ m : ℕ, m ≤ L → 0 ≤ mhHeight p m) ∧ mhHeight p L = h

/-- `p` started at height `h` stays nonnegative and ends at `0`. -/
private def mhSuffixGood {L : ℕ} (p : Fin L → Fin 3) (h : ℤ) : Prop :=
  (∀ m : ℕ, m ≤ L → 0 ≤ h + mhHeight p m) ∧ h + mhHeight p L = 0

/-- Snoc decomposition of length-`L+1` paths. -/
private def mhSnocEquiv (L : ℕ) :
    (Fin L → Fin 3) × Fin 3 ≃ (Fin (L + 1) → Fin 3) where
  toFun := fun q => Fin.snoc (α := fun _ => Fin 3) q.1 q.2
  invFun := fun p => (Fin.init (α := fun _ => Fin 3) p, p (Fin.last L))
  left_inv := by
    intro q
    obtain ⟨α, x⟩ := q
    apply Prod.ext
    · change Fin.init (α := fun _ => Fin 3)
        (Fin.snoc (α := fun _ => Fin 3) α x) = α
      exact Fin.init_snoc _ _
    · change Fin.snoc (α := fun _ => Fin 3) α x (Fin.last L) = x
      exact Fin.snoc_last _ _
  right_inv := by
    intro p
    change Fin.snoc (α := fun _ => Fin 3)
      (Fin.init (α := fun _ => Fin 3) p) (p (Fin.last L)) = p
    exact Fin.snoc_init_self p

-- Suffix count. -----------------------------------------------------------------

/-- Cons decomposition of length-`L+1` paths. -/
private def mhConsEquiv (L : ℕ) :
    Fin 3 × (Fin L → Fin 3) ≃ (Fin (L + 1) → Fin 3) :=
  Fin.consEquiv (fun _ => Fin 3)

/-- The forced shape of a path with a hump at `(i, j)`: up at `i`, flats between,
down at `j`. -/
private def mhIsShape {n : ℕ} (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  p i = 2 ∧ (∀ r : Fin n, i.val < r.val → r.val < j.val → p r = 1) ∧ p j = 0

/-- Glue a prefix and suffix into a full path with the forced shape. -/
private def mhGlue {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3) (r : Fin n) :
    Fin 3 :=
  if h1 : r.val < i.val then α ⟨r.val, h1⟩
  else if _h2 : r.val = i.val then 2
  else if _h3 : r.val < j.val then 1
  else if _h4 : r.val = j.val then 0
  else β ⟨r.val - j.val - 1, by
    have _hr := r.is_lt
    have _hj := j.is_lt
    omega⟩

private theorem mhGlue_of_lt {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr : r.val < i.val) :
    mhGlue _hij α β r = α ⟨r.val, hr⟩ := by
  unfold mhGlue
  rw [dite_eq_left hr]

private theorem mhGlue_eq_i {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr : r.val = i.val) :
    mhGlue _hij α β r = 2 := by
  unfold mhGlue
  rw [dite_eq_right (by omega : ¬ r.val < i.val), dite_eq_left hr]

private theorem mhGlue_of_between {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr1 : i.val < r.val) (hr2 : r.val < j.val) :
    mhGlue _hij α β r = 1 := by
  unfold mhGlue
  rw [dite_eq_right (by omega : ¬ r.val < i.val),
    dite_eq_right (by omega : ¬ r.val = i.val), dite_eq_left hr2]

private theorem mhGlue_eq_j {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr : r.val = j.val) :
    mhGlue _hij α β r = 0 := by
  unfold mhGlue
  rw [dite_eq_right (by omega : ¬ r.val < i.val),
    dite_eq_right (by omega : ¬ r.val = i.val),
    dite_eq_right (by omega : ¬ r.val < j.val), dite_eq_left hr]

private theorem mhGlue_of_after {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr : j.val < r.val) :
    mhGlue _hij α β r =
      β ⟨r.val - j.val - 1, by
        have _hrn := r.is_lt
        have _hj := j.is_lt
        omega⟩ := by
  unfold mhGlue
  rw [dite_eq_right (by omega : ¬ r.val < i.val),
    dite_eq_right (by omega : ¬ r.val = i.val),
    dite_eq_right (by omega : ¬ r.val < j.val),
    dite_eq_right (by omega : ¬ r.val = j.val)]

/-- Prefix part of a shaped path. -/
private def mhShapeFst {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (p : Fin n → Fin 3) (r : Fin i.val) : Fin 3 :=
  p ⟨r.val, by
    have _hs := r.is_lt
    have _hi := i.is_lt
    omega⟩

/-- Suffix part of a shaped path. -/
private def mhShapeSnd {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (p : Fin n → Fin 3) (r : Fin (n - 1 - j.val)) : Fin 3 :=
  p ⟨j.val + 1 + r.val, by
    have _hs := r.is_lt
    have _hj := j.is_lt
    omega⟩

private def mhShapeEquiv {n : ℕ} {i j : Fin n} (hij : i.val < j.val) :
    {p : Fin n → Fin 3 // mhIsShape p i j} ≃
      (Fin i.val → Fin 3) × (Fin (n - 1 - j.val) → Fin 3) where
  toFun := fun q => (fun s => mhShapeFst hij q.1 s, fun s => mhShapeSnd hij q.1 s)
  invFun := fun q => ⟨mhGlue hij q.1 q.2,
    mhGlue_eq_i hij q.1 q.2 rfl,
    fun r hr1 hr2 => mhGlue_of_between hij q.1 q.2 hr1 hr2,
    mhGlue_eq_j hij q.1 q.2 rfl⟩
  left_inv := by
    intro pp
    obtain ⟨p, h1, h2, h3⟩ := pp
    apply Subtype.ext
    change mhGlue hij (fun s => mhShapeFst hij p s)
        (fun s => mhShapeSnd hij p s) = p
    apply funext
    intro r
    by_cases hr1 : r.val < i.val
    · rw [mhGlue_of_lt hij _ _ hr1]
      unfold mhShapeFst
      congr 1
    · by_cases hr2 : r.val = i.val
      · have hri : r = i := Fin.ext hr2
        subst hri
        rw [mhGlue_eq_i hij _ _ rfl]
        exact h1.symm
      · by_cases hr3 : r.val < j.val
        · have hbt : i.val < r.val := by omega
          rw [mhGlue_of_between hij _ _ hbt hr3]
          exact (h2 r hbt hr3).symm
        · by_cases hr4 : r.val = j.val
          · have hrj : r = j := Fin.ext hr4
            subst hrj
            rw [mhGlue_eq_j hij _ _ rfl]
            exact h3.symm
          · have hlt : j.val < r.val := by omega
            rw [mhGlue_of_after hij _ _ hlt]
            change mhShapeSnd hij p ⟨r.val - j.val - 1, _⟩ = p r
            unfold mhShapeSnd
            congr 1
            apply Fin.ext
            change j.val + 1 + (r.val - j.val - 1) = r.val
            have _hrn := r.is_lt
            have _hj := j.is_lt
            omega
  right_inv := by
    intro q
    obtain ⟨α, β⟩ := q
    change (fun s => mhShapeFst hij (mhGlue hij α β) s,
      fun s => mhShapeSnd hij (mhGlue hij α β) s) = (α, β)
    apply Prod.ext
    · apply funext
      intro s
      change mhGlue hij α β ⟨s.val, _⟩ = α s
      rw [mhGlue_of_lt hij α β (by have _hs := s.is_lt; omega)]
    · apply funext
      intro s
      change mhGlue hij α β ⟨j.val + 1 + s.val, _⟩ = β s
      have hlt : j.val < j.val + 1 + s.val := by omega
      rw [mhGlue_of_after hij α β hlt]
      congr 1
      apply Fin.ext
      change j.val + 1 + s.val - j.val - 1 = s.val
      have _hs := s.is_lt
      have _hj := j.is_lt
      omega
end MetaMathlibExt
