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
def mhStep : Fin 3 → ℤ := fun s => (s.val : ℤ) - 1

/-- Copy of the Wanted `IsMotzkin` predicate with `mhStep`. -/
def mhIsMotzkin (n : ℕ) (p : Fin n → Fin 3) : Prop :=
  (∀ m : ℕ, m ≤ n →
    0 ≤ ∑ i : Fin n, if i.val < m then mhStep (p i) else 0) ∧
  ∑ i : Fin n, mhStep (p i) = 0

/-- Copy of the Wanted `IsHump` predicate with `mhStep`. -/
def mhIsHump (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  i.val < j.val ∧
  mhStep (p i) = 1 ∧
  mhStep (p j) = -1 ∧
  (∀ r : Fin n, i.val < r.val → r.val < j.val → mhStep (p r) = 0) ∧
  (∑ r : Fin n, if r.val ≤ i.val then mhStep (p r) else 0) = (k : ℤ)

/-- Copy of the Wanted `IsPeak` predicate with `mhStep`. -/
def mhIsPeak (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  mhIsHump n k p i j ∧ j.val = i.val + 1

/-- Number of nonnegative Motzkin prefixes of length `L` ending at height `h`. -/
def mhCount : ℕ → ℤ → ℕ
  | 0, h => if h = 0 then 1 else 0
  | L + 1, h => if h < 0 then 0 else mhCount L (h - 1) + mhCount L h + mhCount L (h + 1)

/-- Number of nonnegative flat-free (Dyck-like) prefixes of length `d` ending at `h`. -/
def mhDyckCount : ℕ → ℤ → ℕ
  | 0, h => if h = 0 then 1 else 0
  | d + 1, h => if h < 0 then 0 else mhDyckCount d (h - 1) + mhDyckCount d (h + 1)

/-- Step of `p` at index `r`, or `0` past the end. -/
def mhStepAt {L : ℕ} (p : Fin L → Fin 3) (r : ℕ) : ℤ :=
  if h : r < L then mhStep (p ⟨r, h⟩) else 0

/-- Height of `p` after `m` steps. -/
def mhHeight {L : ℕ} (p : Fin L → Fin 3) (m : ℕ) : ℤ :=
  ∑ r ∈ Finset.range m, mhStepAt p r

/-- `p` stays nonnegative and ends at height `h`. -/
def mhPrefixGood {L : ℕ} (p : Fin L → Fin 3) (h : ℤ) : Prop :=
  (∀ m : ℕ, m ≤ L → 0 ≤ mhHeight p m) ∧ mhHeight p L = h

/-- `p` started at height `h` stays nonnegative and ends at `0`. -/
def mhSuffixGood {L : ℕ} (p : Fin L → Fin 3) (h : ℤ) : Prop :=
  (∀ m : ℕ, m ≤ L → 0 ≤ h + mhHeight p m) ∧ h + mhHeight p L = 0

/-- Snoc decomposition of length-`L+1` paths. -/
def mhSnocEquiv (L : ℕ) :
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
def mhConsEquiv (L : ℕ) :
    Fin 3 × (Fin L → Fin 3) ≃ (Fin (L + 1) → Fin 3) :=
  Fin.consEquiv (fun _ => Fin 3)

/-- The forced shape of a path with a hump at `(i, j)`: up at `i`, flats between,
down at `j`. -/
def mhIsShape {n : ℕ} (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  p i = 2 ∧ (∀ r : Fin n, i.val < r.val → r.val < j.val → p r = 1) ∧ p j = 0

/-- Glue a prefix and suffix into a full path with the forced shape. -/
def mhGlue {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
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

end MetaMathlibExt
