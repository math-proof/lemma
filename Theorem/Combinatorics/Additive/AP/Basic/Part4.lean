/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Algebra.Module.NatInt
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import Def.Combinatorics.Additive.AP.Basic.Part4
variable {α : Type*} [AddCommMonoid α]

/-! # Arithmetic progressions -/


namespace Set.IsAPOfLengthFree

/-- The extremal cardinality is at most the size of `{1, ..., N}`. -/
theorem maxCard_le (k N : ℕ) : maxCard k N ≤ N :=
  by
    classical
    unfold maxCard
    exact Nat.findGreatest_le N

/-- An extremal progression-free subset attaining `maxCard` exists. -/
theorem maxCard_spec (k N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧
      S.card = maxCard k N ∧ S.IsAPOfLengthFree k := by
  classical
  unfold maxCard
  refine Nat.findGreatest_spec
    (P := fun m ↦ ∃ S : Finset ℕ,
      S ⊆ Finset.Icc 1 N ∧ S.card = m ∧ S.IsAPOfLengthFree k)
    (Nat.zero_le N) ?_
  refine ⟨∅, Finset.empty_subset _, rfl, ?_⟩
  intro t ht hAP
  have ht' : t ⊆ (∅ : Set ℕ) := by simpa using ht
  have ht0 : t = ∅ := Set.subset_empty_iff.mp ht'
  subst t
  have hk : (k : ℕ∞) = 0 := by simpa using hAP.card.symm
  simp [hk]

/-- Every admissible subset has cardinality at most `maxCard`. -/
theorem card_le_maxCard {S : Finset ℕ} {k N : ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hfree : S.IsAPOfLengthFree k) :
    S.card ≤ maxCard k N := by
  classical
  unfold maxCard
  apply Nat.le_findGreatest
  · exact (Finset.card_le_card hS).trans_eq (Nat.card_Icc 1 N)
  · exact ⟨S, hS, rfl, hfree⟩

end Set.IsAPOfLengthFree
