import Mathlib
import sympy.Basic
open Set


namespace SetTheory

/--
[de_morgan_laws](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/SetTheory/Basic.lean)
-/
@[path]
lemma de_morgan_laws
  {A B C : Set α} :
-- imply
  (B ∪ C)ᶜ = Bᶜ ∩ Cᶜ ∧ (B ∩ C)ᶜ = Bᶜ ∪ Cᶜ ∧ A \ (B ∪ C) = (A \ B) ∩ (A \ C) ∧ A \ (B ∩ C) = (A \ B) ∪ (A \ C) :=
-- proof
  ⟨compl_union B C, compl_inter B C, diff_inter_diff.symm, Set.diff_inter⟩

end SetTheory

namespace SetTheory

/--
[well_ordering_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/SetTheory/Basic.lean)
-/
@[path]
lemma well_ordering_nat
  {A B C : Set α}
  {S : Set ℕ}
-- given
  (hS : S.Nonempty) :
-- imply
  ∃ x ∈ S, ∀ y ∈ S, x ≤ y := by
-- proof
  classical
  have ⟨n, hn⟩ := hS
  exact ⟨Nat.find ⟨n, hn⟩, Nat.find_spec ⟨n, hn⟩, fun y hy => Nat.find_min' ⟨n, hn⟩ hy⟩

end SetTheory

namespace SetTheory

/--
[induction_principle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/SetTheory/Basic.lean)
-/
@[path]
lemma induction_principle
  {A B C : Set α}
  {base : P 1}
-- given
  (P : ℕ → Prop)
  (step : ∀ m : ℕ, P m → P (m + 1)) :
-- imply
  ∀ n : ℕ, n ≥ 1 → P n := by
-- proof
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => exact base
    | succ k' => exact step _ (ih (by omega))
end SetTheory
namespace SetTheory

end SetTheory

namespace SetTheory

/--
[set_relations](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/SetTheory/Basic.lean)
-/
@[path]
lemma set_relations
  {A B : Set α} :
-- imply
  (A ⊆ B ↔ ∀ a, a ∈ A → a ∈ B) ∧ (A = B ↔ A ⊆ B ∧ B ⊆ A) ∧ (A ⊂ B ↔ A ⊆ B ∧ A ≠ B) :=
-- proof
  ⟨Iff.rfl, Set.Subset.antisymm_iff, Set.ssubset_iff_subset_ne⟩

end SetTheory


-- created on 2026-10-23
