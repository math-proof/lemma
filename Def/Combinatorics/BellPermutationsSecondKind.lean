/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring


namespace MetaMathlibExt

/-! # Bell permutations of the second kind
-/

/-- Restricted growth function condition. -/
def IsRGF {n : ℕ} (f : Fin n → Fin n) : Prop :=
  ∀ i : Fin n, ∀ j : Fin n, j.val < (f i).val → ∃ i₀ : Fin n, i₀.val < i.val ∧ f i₀ = j

/-- The Bell permutation of the second kind associated to `f`. -/
def bellPerm {n : ℕ} (f : Fin n → Fin n) : Equiv.Perm (Fin n) :=
  ((List.finRange n).map fun i => Equiv.swap i (f i)).prod

/-- Number of weak excedances of a permutation. -/
def numWeak {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  Fintype.card {i : Fin n // i ≤ σ i}

/-- `f` never exceeds the identity. -/
def Subdiag {n : ℕ} (f : Fin n → Fin n) : Prop := ∀ i : Fin n, (f i).val ≤ i.val

/-- Number of distinct values of `f`. -/
def numVals {n : ℕ} (f : Fin n → Fin n) : ℕ := (Finset.univ.image f).card

end MetaMathlibExt
